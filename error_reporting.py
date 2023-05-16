import sys
import dsa
import assume_prove as ap
from typing import NamedTuple, Optional, Set, Tuple
from typing_extensions import assert_never
import source
import smt
from provenance import *
import nip

# REVIEW: @mathieup do you reckon this should go in dsa.py. I am sick of having to type these all out completely.
DSANode = source.Node[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]
DSAExprT = source.ExprT[dsa.Incarnation[source.ProgVarName | nip.GuardVarName]]


def eprint(*args, **kwargs) -> None:
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
    return False


def expr_all_pointervalidops(e: DSAExprT) -> bool:
    #TODO: When we emit PValid
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


def extract_and_print_why(func: dsa.Function, reason: FailureReason, node: DSANode) -> source.NodeName:
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

def debug_func_smt(func: dsa.Function) -> Tuple[FailureReason, source.NodeName, source.NodeName]:
    """
    To enter this function, we make the assumption that verifying func results in SAT. 
    This is an assumption. 

    :param func: Function to debug. 
    :result: Returns the reason of failure, node name of the failing assertion, node name of where the bad use is.
    """

    prog = ap.make_prog(func)
    prev_node_name: Optional[source.NodeName] = None
    for node_name in func.traverse_topologically(skip_err_and_ret=True):
        smtlib = smt.make_smtlib(prog, ap.node_ok_name(node_name))
        sats = tuple(smt.send_smtlib(smtlib, smt.SolverCVC5()))
        if sats[2] == smt.CheckSatResult.UNSAT:
            assert prev_node_name is not None
            eprint(f"Verification failed at {prev_node_name}")
            prev_node = func.nodes[prev_node_name]
            reason = determine_reason(prev_node)
            print_reason(reason)
            use_node_name = extract_and_print_why(func, reason, prev_node)
            return (reason, node_name, use_node_name)
        prev_node_name = node_name
    assert False, "This should never happen"
