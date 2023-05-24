import sys
import dsa
import assume_prove as ap
from typing import Callable, NamedTuple, Optional, Set, Tuple
from typing_extensions import assert_never
import source
import smt
from provenance import *
import nip
import subprocess
import textwrap
import utils
import parser_combinator as pc
from dot_graph import pretty_safe_expr, pretty_safe_update
import smt_parser
import ghost_code
from rich.console import Console

econsole = Console(stderr=True)

# REVIEW: @mathieup do you reckon this should go in dsa.py. I am sick of having to type these all out completely.
DSANode = source.Node[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]
DSAExprT = source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]


def eprint(*args, **kwargs) -> None:  # type: ignore
    if "style" not in kwargs:
        kwargs["style"] = "bold red"
    econsole.print(*args, **kwargs)


class OverflowFailure(NamedTuple):
    pass


class UnderflowFailure(NamedTuple):
    pass


class OverOrUnderflowFailure(NamedTuple):
    pass


class UnknownFailure(NamedTuple):
    pass


class UnInitialised(NamedTuple):
    pass


class UnAlignedMemory(NamedTuple):
    pass


class InvalidMemory(NamedTuple):
    pass


class NodeCallPreCondFailure(NamedTuple):
    pass


class LoopInvariantObligFailure(NamedTuple):
    pass


class FnPostCondFailure(NamedTuple):
    pass


FailureReason = OverflowFailure | UnderflowFailure | UnknownFailure | OverOrUnderflowFailure | UnInitialised | UnAlignedMemory | InvalidMemory | LoopInvariantObligFailure | NodeCallPreCondFailure | FnPostCondFailure


def expr_common_arith() -> Set[source.Operator]:
    return {source.Operator.EQUALS, source.Operator.SIGNED_LESS, source.Operator.SIGNED_LESS_EQUALS, source.Operator.AND, source.Operator.OR}


def check_ops(e: DSAExprT, allowed_ops: Set[source.Operator]) -> bool:
    valid: bool = True

    def visitor(v: DSAExprT) -> None:
        if isinstance(v, source.ExprOp):
            if v.operator not in allowed_ops:
                nonlocal valid
                valid = False
        elif isinstance(v, source.ExprNum):
            pass
        elif isinstance(v, source.ExprVar):
            pass
        else:
            pass
    source.visit_expr(e, visitor)
    return valid


def expr_all_adds(e: DSAExprT) -> bool:
    allowed_ops = {source.Operator.PLUS,
                   source.Operator.TIMES}.union(expr_common_arith())
    return check_ops(e, allowed_ops)


def expr_all_subtract(e: DSAExprT) -> bool:
    allowed_ops = {source.Operator.MINUS,
                   source.Operator.DIVIDED_BY}.union(expr_common_arith())
    return check_ops(e, allowed_ops)


def expr_all_arith(e: DSAExprT) -> bool:
    allowed_ops = {source.Operator.MINUS,
                   source.Operator.PLUS,
                   source.Operator.TIMES,
                   source.Operator.DIVIDED_BY}.union(expr_common_arith())
    return check_ops(e, allowed_ops)


def expr_all_pointeralignops(e: DSAExprT) -> bool:
    # TODO: When we handle memory
    return False


def expr_all_pointervalidops(e: DSAExprT) -> bool:
    # TODO: When we handle memory
    return False


def determine_reason(node: DSANode) -> FailureReason:
    # We certainly shouldn't see these
    assert not isinstance(node, source.NodeBasic)
    assert not isinstance(node, source.NodeCall)
    assert not isinstance(node, source.NodeEmpty)
    if isinstance(node, source.NodeEmpty):
        # We really shouldn't see this.
        return UnknownFailure()
    elif isinstance(node.origin, ProvenanceNipGuard):
        return UnInitialised()
    elif isinstance(node.origin, ProvenanceGraphLang):
        assert isinstance(node, source.NodeCond)
        if expr_all_adds(node.expr):
            return OverflowFailure()
        elif expr_all_subtract(node.expr):
            return UnderflowFailure()
        elif expr_all_arith(node.expr):
            return OverOrUnderflowFailure()
        elif expr_all_pointeralignops(node.expr):
            return UnAlignedMemory()
        elif expr_all_pointervalidops(node.expr):
            return InvalidMemory()
        else:
            return UnknownFailure()
    elif isinstance(node.origin, ProvenancePreCond):
        assert False, "didn't expect to determine a pre cond node as the failure reason"
    elif isinstance(node.origin, ProvenanceLoopInvariantObligation):
        return LoopInvariantObligFailure()
    elif isinstance(node.origin, ProvenanceNipUpdate):
        assert False, "didn't expect to see a nip update as being the failure reason"
    elif isinstance(node.origin, ProvenanceDSAJoiner):
        assert False, "didn't expect to see dsa joiner as being the failure reason"
    elif isinstance(node.origin, ProvenancePreCondFnObligation):
        return NodeCallPreCondFailure()
    elif isinstance(node.origin, ProvenancePostCondFnAssume):
        assert False, "didn't expect to see a post condition assumption as being the failure reason"
    elif isinstance(node.origin, ProvenanceLoopInvariantAssume):
        assert False, "didn't expect to see a loop invariant assumption as being the failure reason"
    elif isinstance(node.origin, ProvenancePostCond):
        return FnPostCondFailure()
    else:
        assert_never(node.origin)


def print_reason(reason: FailureReason) -> None:
    if isinstance(reason, UnInitialised):
        eprint("uninitialised variable")
    elif isinstance(reason, UnknownFailure):
        eprint("unable to determine failure reason")
    elif isinstance(reason, UnderflowFailure):
        eprint("hint: variable likely underflows")
    elif isinstance(reason, OverflowFailure):
        eprint("hint: variable likely overflows")
    elif isinstance(reason, UnAlignedMemory):
        eprint("unaligned memory")
    elif isinstance(reason, InvalidMemory):
        eprint("invalid memory")
    elif isinstance(reason, OverOrUnderflowFailure):
        eprint("hint: likely invalid arithmetic causing overflow or underflow")
    elif isinstance(reason, NodeCallPreCondFailure):
        eprint("failed to satisfy function precondition")
    elif isinstance(reason, LoopInvariantObligFailure):
        eprint("failed to prove loop invariant")
    elif isinstance(reason, FnPostCondFailure):
        eprint("failed to prove function post condition")
    else:
        assert_never(reason)


def human_var_nip(src: source.ExprVarT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> str:
    varname = str(src.name.base)
    splitvarname = varname.split('#v#assigned')
    assert len(
        splitvarname) == 2, "This is not supposed to happen, there is a bug in the error reporting python code"
    human_varname = splitvarname[0].split('___')
    assert len(human_varname) == 2, "This is not supposed to happen"
    return human_varname[0]


def human_var(src: source.ExprVarT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> str:
    varname = str(src.name.base)
    human_varname = varname.split('___')
    assert len(human_varname) == 2, "This is not supposed to happen"
    return human_varname[0]


def extract_and_print_why(func: dsa.Function, reason: FailureReason, node: DSANode, node_name: source.NodeName) -> Optional[source.NodeName]:
    """Prints debug information for the user and returns the NodeName in which a use caused an assertion to fail

    :param func: Function we are error reporting on, needed for context information. 
    :param reason: Used to determine what kind of extraction and additional checking needs to be done to print a verbose error message
    :param node: The node (always a prove Node) that caused SAT.
    :param node_name: The name of @node

    :return: A successive node name which indicates which use caused the node (parameter) to fail
    """
    if isinstance(reason, UnInitialised):
        assert isinstance(node, source.NodeCond)
        succ_node_name = node.succ_then
        variables = list(
            map(human_var_nip, source.used_variables_in_node(node)))
        assert len(
            variables) > 0, "Makes no sense for no variables to be uninitialised and still have the reason as uninitialised"
        if len(variables) == 1:
            eprint(
                f"{variables[0]} was uninitialised when used, refer to GraphLang at node {succ_node_name}")
        else:
            eprint(
                f"one of {variables} was uninitialised, refer to GraphLang at node {succ_node_name}")
        return succ_node_name
    elif isinstance(reason, OverflowFailure | UnderflowFailure | OverOrUnderflowFailure):
        assert isinstance(node, source.NodeCond)
        failure_str = ""
        if isinstance(reason, OverflowFailure):
            failure_str = "overflow"
        elif isinstance(reason, UnderflowFailure):
            failure_str = "underflow"
        else:
            failure_str = "underflow or overflow"
        variables = list(map(human_var, source.used_variables_in_node(node)))
        succ_node_name = node.succ_then
        succ_node = func.nodes[succ_node_name]
        # a guard is always followed:
        assert isinstance(succ_node, nip.NodeGuard)
        # now the node which causes the overflow
        succ_succ_node_name = succ_node.succ_then
        succ_succ_node = func.nodes[succ_succ_node_name]
        assert isinstance(succ_succ_node, source.NodeBasic)
        if len(variables) == 0:
            assert False, "This should never be the case"
        elif len(variables) == 1:
            eprint(
                f"variable {variables[0]} is involved in an {failure_str}, refer to GraphLang at node {succ_succ_node_name}")
        else:
            eprint(f"one or more of variables", variables,
                   f"leads to an {failure_str} from some interleaving of arithmetic operation(s), refer to GraphLang at node {succ_succ_node_name}")
        return succ_succ_node_name
    elif isinstance(reason, UnknownFailure):
        eprint("got an unknown failure, try normalising the C code and running ubc again")
        return None
    elif isinstance(reason, InvalidMemory):
        # TODO Depends on what we emit for memory ops
        assert False, "TODO"
    elif isinstance(reason, UnAlignedMemory):
        assert False, "TODO"
    elif isinstance(reason, LoopInvariantObligFailure):
        assert isinstance(node, ghost_code.NodeLoopInvariantProofObligation)
        eprint(
            f"The loop invariant proof obligation at node {node_name} was not met")
        return None
    elif isinstance(reason, NodeCallPreCondFailure):
        assert isinstance(node, ghost_code.NodePrecondObligationFnCall)
        succ_node_name = node.succ
        succ_node = func.nodes[succ_node_name]
        assert isinstance(succ_node, source.NodeCall)
        eprint(
            f"call to function {succ_node.fname} did not satisfy it's preconditions")
        return succ_node_name
    elif isinstance(reason, FnPostCondFailure):
        assert isinstance(node, ghost_code.NodePostConditionProofObligation)
        eprint(
            f"function {func.name}'s post condition was not able to be proven")
        # no such thing as a use here
        return None
    else:
        assert_never(reason)


def get_sat(smtlib: smt.SMTLIB) -> Tuple[bool, smt.CheckSatResult]:
    results = tuple(smt.send_smtlib(smtlib, smt.SolverCVC5()))
    sz = len(results)
    assert sz >= 2
    for i in range(0, sz-1):
        if results[i] == smt.CheckSatResult.UNSAT:
            return False, results[-1]
    return True, results[-1]


def pretty_node(node: source.Node[source.VarNameKind]) -> str:
    """ This isn't great in a way, it doesn't print the proper graphlang name it uses the dot format for dsa names"""
    if isinstance(node, source.NodeBasic):
        return "\n".join(pretty_safe_update(u) for u in node.upds)
    elif isinstance(node, source.NodeCond):
        return pretty_safe_expr(node.expr)
    elif isinstance(node, source.NodeCall):
        formatted_rets = ', '.join(pretty_safe_expr(ret) for ret in node.rets)
        args = ', '.join(pretty_safe_expr(arg) for arg in node.args)
        return f"{formatted_rets} = {node.fname}({args})"
    elif isinstance(node, source.NodeAssume):
        assert False, "We should never see a NodeAssume being the reason a SAT was returned"
    elif isinstance(node, source.NodeAssert):
        return pretty_safe_expr(node.expr)
    elif isinstance(node, source.NodeEmpty):
        assert False, "We should never see a NodeEmpty being the reason a SAT was returned"
    else:
        assert_never(node)


def send_smtlib_model(smtlib: smt.SMTLIB, solver_type: smt.SolverType) -> smt.Responses:
    """Send command to any smt solver and returns a boolean per (check-sat)
    """

    with utils.open_temp_file(suffix='.smt2') as (f, fullpath):
        f.write(smtlib)
        f.close()
        p = subprocess.Popen(smt.get_subprocess_file(
            solver_type, fullpath), stderr=subprocess.PIPE, stdout=subprocess.PIPE)
        p.wait()
    assert p.stderr is not None
    assert p.stdout is not None
    if p.returncode != 0:
        print("stderr:")
        print(textwrap.indent(p.stdout.read().decode('utf-8'), '   '))
        sys.exit(1)
    lines = p.stdout.read().decode('utf-8')
    fn = smt_parser.parse_responses()
    res = fn(lines)
    assert not isinstance(
        res, pc.ParseError), "The smt parser doesn't handle the output here, only a small subset of SMT is parsed at the moment"
    responses, _ = res
    return responses


def get_relevant_responses(node_vars: Set[source.ExprVarT[ap.VarName]], responses: smt.Responses) -> None:
    lambda_fn: Callable[[smt.Identifier], bool] = lambda x: x != smt.identifier(
        ap.node_ok_name(source.NodeNameErr))
    rel_vars = set(filter(
        lambda_fn,
        map(lambda x: smt.identifier(x.name), node_vars)
    )
    )
    for res in responses:
        if isinstance(res, smt.CheckSatResponse):
            continue

        for defFun in res:
            if defFun.symbol in rel_vars:
                eprint(defFun)


def node_dsa_to_node_ap(node: DSANode) -> source.Node[ap.VarName]:
    if isinstance(node, source.NodeEmpty):
        return source.NodeEmpty(succ=node.succ)
    elif isinstance(node, source.NodeBasic):
        def convert_update(upd: source.Update[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]) -> source.Update[ap.VarName]:
            new_var = ap.convert_expr_dsa_vars_to_ap(upd.var)
            new_expr = ap.convert_expr_dsa_vars_to_ap(upd.expr)
            return source.Update(var=new_var, expr=new_expr)
        upds = tuple(map(convert_update, node.upds))
        return source.NodeBasic(origin=node.origin, upds=upds, succ=node.succ)

    elif isinstance(node, source.NodeAssume):
        new_expr = ap.convert_expr_dsa_vars_to_ap(node.expr)
        return source.NodeAssume(origin=node.origin, succ=node.succ, expr=new_expr)
    elif isinstance(node, source.NodeAssert):
        new_expr = ap.convert_expr_dsa_vars_to_ap(node.expr)
        return source.NodeAssert(origin=node.origin, succ=node.succ, expr=new_expr)
    elif isinstance(node, source.NodeCall):
        args = tuple(map(ap.convert_expr_dsa_vars_to_ap, node.args))
        rets = tuple(map(ap.convert_expr_dsa_vars_to_ap, node.rets))
        return source.NodeCall(origin=node.origin, succ=node.succ, args=args, rets=rets, fname=node.fname)
    elif isinstance(node, source.NodeCond):
        new_expr = ap.convert_expr_dsa_vars_to_ap(node.expr)
        return source.NodeCond(origin=node.origin, expr=new_expr, succ_then=node.succ_then, succ_else=node.succ_else)
    else:
        assert_never(node)


def debug_func_smt(func: dsa.Function) -> Tuple[FailureReason, source.NodeName, Optional[source.NodeName]]:
    prog = ap.make_prog(func)
    q: set[source.NodeName] = set([func.cfg.entry])
    not_taken_path: set[source.NodeName] = set([])
    visited: set[source.NodeName] = set([])
    while len(q) != 0:
        node_name = q.pop()
        visited = visited.union(set([node_name]))
        node = func.nodes[node_name]
        not_taken_path_and_node = not_taken_path.union(set([node_name]))
        node_smtlib = smt.make_smtlib(prog, not_taken_path_and_node)
        consistent, node_sat = get_sat(node_smtlib)
        assert consistent
        # we do not care about the Err and Ret node
        successors = list(
            filter(lambda x: x != source.NodeNameErr and x != source.NodeNameRet and ((node_name, x) not in func.cfg.back_edges), func.cfg.all_succs[node_name]))
        successors_smtlib = smt.make_smtlib(
            prog, not_taken_path.union(set(successors)))
        _, successors_sat = get_sat(successors_smtlib)
        if successors_sat == smt.CheckSatResult.SAT and node_sat == smt.CheckSatResult.UNSAT:
            # This is our error node
            reason = determine_reason(node)
            print_reason(reason)

            # used_node_name is optional because could not determine the reason
            used_node_name = extract_and_print_why(
                func, reason, node, node_name)
            if used_node_name is not None:
                used_node = func.nodes[used_node_name]
                used_node_as_ap = node_dsa_to_node_ap(used_node)

                eprint("HINT: SUSPECTED STATEMENT",
                       justify="center", style="red on white")
                eprint(pretty_node(used_node_as_ap), style="magenta bold")

            succ_smtlib_with_model = smt.make_smtlib(
                prog, not_taken_path.union(set(successors)), with_model=True)
            succ_model = send_smtlib_model(
                succ_smtlib_with_model, smt.SolverZ3())

            node_vars = set(
                map(ap.convert_expr_var, source.used_variables_in_node(node)))

            # need to get AP name
            eprint("VARIABLES USED IN ASSERTION",
                   justify="center", style="red on white")
            get_relevant_responses(node_vars, succ_model)

            return (reason, node_name, used_node_name)

        # When len(successors) == 1 and it is a NodeCond, it is because the succ_else path to NodeNameErr was trimmed
        # This is handled above, so we skip it.
        if isinstance(node, source.NodeCond) and len(successors) != 1:
            node1 = successors[0]
            node2 = successors[1]
            not_taken_path_and_succ1 = not_taken_path.union(set([node1]))
            not_taken_path_and_succ2 = not_taken_path.union(set([node2]))
            succ_node1_smtlib = smt.make_smtlib(prog, not_taken_path_and_succ1)
            succ_node2_smtlib = smt.make_smtlib(prog, not_taken_path_and_succ2)
            succ_node1_consistent, succ_node1_sat = get_sat(succ_node1_smtlib)
            succ_node2_consistent, succ_node2_sat = get_sat(succ_node2_smtlib)
            if succ_node1_sat == smt.CheckSatResult.UNSAT and succ_node2_sat == smt.CheckSatResult.UNSAT:
                if succ_node1_consistent:
                    q = q.union(set([node1]))
                elif succ_node2_consistent:
                    q = q.union(set([node2]))
                else:
                    assert False, "one path has to be consistent"
                # EDGE case take any path but do not add to not_taken_path
                q = q.union(set([node1]))
            elif succ_node1_sat == smt.CheckSatResult.UNSAT and succ_node2_sat == smt.CheckSatResult.SAT:
                q.add(node1)
                not_taken_path.add(node2)
            elif succ_node2_sat == smt.CheckSatResult.UNSAT and succ_node1_sat == smt.CheckSatResult.SAT:
                q.add(node2)
                not_taken_path.add(node1)
            else:
                assert False, "When checking for result of conditional both paths returned SAT, this is not expected"
        else:
            q = q.union(set(successors))
    assert False, "This was reached because we failed to diagnose an error - either this function succeeds or some edge case is missing for error handling"
