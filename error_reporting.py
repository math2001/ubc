import sys
import dsa
import assume_prove as ap
from typing import NamedTuple, Optional, Set, Tuple
from typing_extensions import assert_never
import source
import smt
from provenance import *
import nip
import subprocess
import textwrap
from dot_graph import pretty_expr, pretty_safe_expr, pretty_safe_update
import smt_parser

# REVIEW: @mathieup do you reckon this should go in dsa.py. I am sick of having to type these all out completely.
DSANode = source.Node[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]
DSAExprT = source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]


def eprint(*args, **kwargs) -> None: # type: ignore
    print(*args, file=sys.stderr, **kwargs)

class OverflowFailure(NamedTuple):
    pass


class UnderflowFailure(NamedTuple):
    pass


class UnknownFailure(NamedTuple):
    pass


class UnInitialised(NamedTuple):
    pass


class UnAlignedMemory(NamedTuple):
    pass


class InvalidMemory(NamedTuple):
    pass


FailureReason = OverflowFailure | UnderflowFailure | UnknownFailure | UnInitialised | UnAlignedMemory | InvalidMemory


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
    allowed_ops = {source.Operator.PLUS, source.Operator.TIMES}.union(expr_common_arith()) 
    return check_ops(e, allowed_ops)

def expr_all_subtract(e: DSAExprT) -> bool:
    allowed_ops = {source.Operator.MINUS, source.Operator.DIVIDED_BY}.union(expr_common_arith())
    return check_ops(e, allowed_ops)

def expr_all_pointeralignops(e: DSAExprT) -> bool:
    # TODO: When we handle memory
    return False


def expr_all_pointervalidops(e: DSAExprT) -> bool:
    #TODO: When we handle memory
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
        elif expr_all_pointeralignops(node.expr):
            return UnAlignedMemory()
        elif expr_all_pointervalidops(node.expr):
            return InvalidMemory()
    return UnknownFailure()


def print_reason(reason: FailureReason) -> None:
    if isinstance(reason, UnInitialised):
        eprint("uninitialised variable")
    elif isinstance(reason, UnknownFailure):
        eprint("unable to determine failure reason")
    elif isinstance(reason, UnderflowFailure):
        eprint("variable underflows")
    elif isinstance(reason, OverflowFailure):
        eprint("variable overflows")
    elif isinstance(reason, UnAlignedMemory):
        eprint("unaligned memory")
    elif isinstance(reason, InvalidMemory):
        eprint("invalid memory")
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


def extract_and_print_why(func: dsa.Function, reason: FailureReason, node: DSANode) -> Optional[source.NodeName]:
    """Prints debug information for the user and returns the NodeName in which a use caused an assertion to fail

    :param func: Function we are error reporting on, needed for context information. 
    :param reason: Used to determine what kind of extraction and additional checking needs to be done to print a verbose error message
    :param node: The node (always a prove Node) that caused SAT.

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
            eprint(f"{variables[0]} was uninitialised when used, refer to GraphLang at node {succ_node_name}")
        else:
            eprint(f"one of {variables} was uninitialised, refer to GraphLang at node {succ_node_name}")
        return succ_node_name
    elif isinstance(reason, OverflowFailure | UnderflowFailure):
        assert isinstance(node, source.NodeCond)
        failure_str = "overflow" if isinstance(reason, OverflowFailure) else "underflow"
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
            eprint(f"variable {variables[0]} is involved in an {failure_str}, refer to GraphLang at node {succ_succ_node_name}")
        else:
            eprint(f"one or more of variables", variables,
                  f"leads to an {failure_str} from some interleaving of arithmetic operation(s), refer to GraphLang at node {succ_succ_node_name}")
        return succ_succ_node_name  
    elif isinstance(reason, UnknownFailure):
        assert False, "Some condition wasn't handled"
    elif isinstance(reason, InvalidMemory):
        assert False, "TODO"
    elif isinstance(reason, UnAlignedMemory):
        assert False, "TODO"
    else:
        assert_never(reason)

def get_sat(smtlib: smt.SMTLIB) -> smt.CheckSatResult:
    results = tuple(smt.send_smtlib(smtlib, smt.SolverCVC5()))
    return results[-1]


def pretty_node(node: DSANode) -> str:
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

    with smt.open_temp_file(suffix='.smt2') as (f, fullpath):
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
    print(lines)
    f = smt_parser.parse_responses()
    res = f(lines)
    print(res)
    exit(1)

def debug_func_smt(func: dsa.Function) -> Tuple[FailureReason, source.NodeName, Optional[source.NodeName]]:
    prog = ap.make_prog(func)
    q: set[source.NodeName] = set([func.cfg.entry])
    not_taken_path: set[source.NodeName] = set([])
    while len(q) != 0:
        node_name = q.pop()
        print(node_name)
        node = func.nodes[node_name]
        not_taken_path_and_node = not_taken_path.union(set([node_name]))
        node_smtlib = smt.make_smtlib(prog, not_taken_path_and_node)
        node_sat = get_sat(node_smtlib)
        # we do not care about the Err node
        successors = list(filter(lambda x: x != source.NodeNameErr, func.cfg.all_succs[node_name]))
        successors_smtlib = smt.make_smtlib(prog, not_taken_path.union(set(successors)))
        successors_sat = get_sat(successors_smtlib)
        if successors_sat == smt.CheckSatResult.SAT and node_sat == smt.CheckSatResult.UNSAT:
            # This is our error node  
            succ_smtlib_with_model = smt.make_smtlib(prog, not_taken_path.union(set(successors)), with_model=True)
            succ_model = tuple(send_smtlib_model(succ_smtlib_with_model, smt.SolverZ3()))
            print(succ_model)
            reason = determine_reason(node)
            print_reason(reason)
            
            # used_node_name is optional because could not determine the reason
            used_node_name = extract_and_print_why(func, reason, node)
            if used_node_name != None:
                used_node = func.nodes[used_node_name]
                print(pretty_node(used_node))
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


            succ_node1_sat = get_sat(succ_node1_smtlib)
            succ_node2_sat = get_sat(succ_node2_smtlib)
            if succ_node1_sat == smt.CheckSatResult.UNSAT and succ_node2_sat == smt.CheckSatResult.UNSAT:
                # EDGE case take any path but do not add to not_taken_path
                q = q.union(set(successors))
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
