from __future__ import annotations
from dataclasses import dataclass
import dataclasses
from enum import Enum, unique
from typing import Callable, Iterable, Mapping, NamedTuple, Sequence, Tuple, Any, Iterator, Dict, TypeAlias
from typing_extensions import assert_never

import abc_cfg
import source
import nip
import ghost_data
import syntax
from provenance import *


@dataclass(frozen=True)
class NodePostConditionProofObligation(source.NodeCond[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodePreconditionAssumption(source.NodeAssume[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeLoopInvariantAssumption(source.NodeAssume[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeLoopInvariantProofObligation(source.NodeCond[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodePrecondObligationFnCall(source.NodeAssert[source.VarNameKind]):
    pass


@dataclass(frozen=True)
class NodeAssumePostCondFnCall(source.NodeAssume[source.VarNameKind]):
    pass


NodeGhostCode = (NodePostConditionProofObligation[source.VarNameKind]
                 | NodePreconditionAssumption[source.VarNameKind]
                 | NodeLoopInvariantAssumption[source.VarNameKind]
                 | NodeLoopInvariantProofObligation[source.VarNameKind]
                 | NodePrecondObligationFnCall[source.VarNameKind]
                 | NodeAssumePostCondFnCall[source.VarNameKind])


class GenericFunction(nip.GenericFunction[source.VarNameKind, source.VarNameKind2]):
    """
    Function pre conditions, post condition, and loop invariants inserted in
    the CFG
    """


Function = GenericFunction[source.ProgVarName |
                           nip.GuardVarName, source.ProgVarName | nip.GuardVarName]


class Insertion(NamedTuple):
    after: source.NodeName
    before: source.NodeName

    node_name: source.NodeName
    mk_node: Callable[[source.NodeName],
                      source.Node[source.ProgVarName | nip.GuardVarName]]


Edge: TypeAlias = tuple[source.NodeName, source.NodeName]


def apply_insertions(func: nip.Function, insertions: Sequence[Insertion]) -> Mapping[source.NodeName, source.Node[source.ProgVarName | nip.GuardVarName]]:
    # edge -> list of insertion to apply on that edge, _in order_ (first is
    # inserted first, etc)

    edge_insertions: dict[Edge, list[Insertion]] = {}
    for insertion in insertions:
        edge = (insertion.after, insertion.before)
        if edge not in edge_insertions:
            edge_insertions[edge] = []
        edge_insertions[edge].append(insertion)

    new_nodes: dict[source.NodeName,
                    source.Node[source.ProgVarName | nip.GuardVarName]] = {}
    for after_name, node in func.nodes.items():

        # construct (and add to the node map) all the insertion nodes
        #   - first one isn't connected
        #   - last one jumps to after_name's successor
        # case split on the type of after_name to connect the first one
        #   - dataclass._replace(...)

        new_nodes[after_name] = node

        for before_name in func.cfg.all_succs[after_name]:
            edge = (after_name, before_name)
            if edge not in edge_insertions:
                continue
            assert len(edge_insertions[edge]) > 0

            for i, insertion in enumerate(edge_insertions[edge]):
                assert insertion.node_name not in new_nodes, f"trying to insert a new node, but the name ({insertion.node_name}) is already taken"
                if i == len(edge_insertions[edge]) - 1:
                    insertion_succ = before_name
                else:
                    insertion_succ = edge_insertions[edge][i+1].node_name
                new_nodes[insertion.node_name] = insertion.mk_node(
                    insertion_succ)

            first_inserted_node_name: source.NodeName = edge_insertions[edge][0].node_name
            # connect node_name to the first insertion node
            if isinstance(node, source.NodeBasic | source.NodeCall | source.NodeEmpty | source.NodeAssume | source.NodeAssert):
                new_nodes[after_name] = dataclasses.replace(new_nodes[after_name],
                                                            succ=first_inserted_node_name)
            elif isinstance(node, source.NodeCond):
                # notice how we replace from new_nodes[after_name], not node
                # this important, because it can be updated multiple times
                # (consider what happens when inserting on both the left and
                # right branch of conditional node)
                if node.succ_then == before_name:
                    new_nodes[after_name] = dataclasses.replace(new_nodes[after_name],
                                                                succ_then=first_inserted_node_name)
                elif node.succ_else == before_name:
                    new_nodes[after_name] = dataclasses.replace(new_nodes[after_name],
                                                                succ_else=first_inserted_node_name)
            else:
                assert_never(node)

    return new_nodes


class GhostVarName(source.ProgVarName):
    pass

# a variable that ends with /subject-arg


class SubjectArgVarName(GhostVarName):
    pass

# a variable that ends with /subject-arg


class CallArgVarName(GhostVarName):
    pass


def subject_arg_var_name(arg: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[GhostVarName]:
    assert arg.name.endswith('/arg'), f"{arg.name!r}"
    return source.ExprVar(arg.typ, SubjectArgVarName(arg.name[:-len('/arg')] + "/subject-arg"))


def call_arg_var_name(arg: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[GhostVarName]:
    assert arg.name.endswith('/arg'), f"{arg.name!r}"
    return source.ExprVar(arg.typ, CallArgVarName(arg.name[:-len('/arg')] + "/call-arg"))


@unique
class Mode(Enum):
    subject = "subject"
    call = "call"


NUM_GHOST_VARIABLES_CPARSER_FUNCTION_CALL = 4  # mem, htd, pms, ghost assertions


def sprinkle_subject_pre_and_post_conditions(func: nip.Function) -> Iterable[Insertion]:
    """
    We assume the precondition holds, stash the initial values with the
    suffix /subject-arg of all the arguments, and then assert that the post
    condition holds at the bottom of the function, replacing the variables
    with suffix /arg (refering to their old value) with the
    suffix /subject-arg(ie. the stashed variables).
    """
    entry_node = func.nodes[func.cfg.entry]
    assert isinstance(entry_node, source.NodeEmpty)

    # a1/subject-arg = a1; a2/subject-arg = a2, ... (for all arguments)
    stash_updates = tuple(source.Update(source.ExprVar(param.typ, SubjectArgVarName(param.name + '/subject-arg')), param)
                          for param in func.signature.parameters)

    yield Insertion(after=func.cfg.entry,
                    before=entry_node.succ,
                    node_name=source.NodeName('stash_initial_args'),
                    mk_node=lambda succ: source.NodeBasic(ProvenanceCallStashInitialArgs(), stash_updates, succ))

    def f(var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[source.ProgVarName | nip.GuardVarName]:
        # this will change with the new way of writting specs
        if not var.name.endswith('/arg'):
            assert False, f"unknown variable {var.name}"

        return subject_arg_var_name(var)

    precondition = source.convert_expr_vars(f, func.ghost.precondition)

    yield Insertion(after=func.cfg.entry,
                    before=entry_node.succ,
                    node_name=source.NodeName('pre_condition'),
                    mk_node=lambda succ: NodePreconditionAssumption(ProvenancePreCond(), precondition, succ))

    def g(var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[source.ProgVarName | nip.GuardVarName]:
        # this will be cleaned up when we implement the new way of writting specs
        if isinstance(var.name, source.CRetSpecialVar):
            assert 0 <= var.name.field_num and var.name.field_num <= len(
                func.signature.returns) - NUM_GHOST_VARIABLES_CPARSER_FUNCTION_CALL
            return func.signature.returns[var.name.field_num]
        elif var.name.endswith("/arg"):
            return subject_arg_var_name(var)
        return var

    converted_post_condition = source.convert_expr_vars(
        g, func.ghost.postcondition)

    assert len(func.cfg.all_preds[source.NodeNameRet]) == 1, ("not to worry, just need to handle the case "
                                                              "where the Ret node has multiple predecessors")

    pred = func.cfg.all_preds[source.NodeNameRet][0]
    yield Insertion(after=pred,
                    before=source.NodeNameRet,
                    node_name=source.NodeName('post_condition'),
                    mk_node=lambda succ: NodePostConditionProofObligation(ProvenancePostCond(), converted_post_condition, succ, source.NodeNameErr))


def sprinkle_loop_invariant(func: nip.Function, lh: source.LoopHeaderName) -> Iterable[Insertion]:
    # TODO
    # ----
    #
    # to generate more readable SMT, we should put the loop invariant into an
    # SMT function. It would be safe to also provide a proof that this
    # function only needs to have for parameter the loop targets.
    #
    # proof sketch: suppose the loop invariant depends on a variable which
    # isn't a loop target. By definition of loop targets, it is never on the
    # lhs of an assignment within the loop, thus it's value is constant, and
    # hence doesn't need to be a parameter. By exhaustion of cases, the
    # invariant's parameters only need to be the loop targets.
    #
    # If a variable isn't a loop target, the incarnation number to use is the
    # one that occurs in the loop header's DSA context (ie. the only incarnation
    # for that variable throughout the loop)
    #
    # UPDATE: this will be fixed when we switch to the new way of writing
    # specs

    # ALL predecessors, including predecessors that follow a back edge

    def f(var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[source.ProgVarName | nip.GuardVarName]:
        if var.name.endswith('/arg'):
            return subject_arg_var_name(var)
        return var

    inv = source.convert_expr_vars(f, func.ghost.loop_invariants[lh])
    for i, pred in enumerate(func.cfg.all_preds[lh], start=1):
        yield Insertion(after=pred,
                        before=lh,
                        node_name=source.NodeName(f'loop_{lh}_latch_{i}'),
                        mk_node=lambda succ: NodeLoopInvariantProofObligation(
                            ProvenanceLoopInvariantObligation(),
                            inv,
                            succ,
                            source.NodeNameErr
                        ))

    for i, nsucc in enumerate(func.cfg.all_succs[lh], start=1):
        yield Insertion(after=lh,
                        before=nsucc,
                        node_name=source.NodeName(f'loop_{lh}_inv_asm_{i}'),
                        mk_node=lambda succ: NodeLoopInvariantAssumption(
                            ProvenanceLoopInvariantAssume(),
                            inv,
                            succ))


def sprinkle_loop_invariants(func: nip.Function) -> Iterable[Insertion]:
    for loop_header in func.loops:
        yield from sprinkle_loop_invariant(func, loop_header)

# def sprinkle_function_call_pre_and_post_condition(func: nip.Function, node_name: source.NodeName) -> Iterable[Insertion]:


def sprinkle_function_call_pre_and_post_condition(func: nip.Function,
                                                  node_name: source.NodeName,
                                                  node: source.NodeCall[source.ProgVarName | nip.GuardVarName],
                                                  signatures: Mapping[str, TemporaryFunctionSignature]) -> Iterable[Insertion]:

    # the parameters are the "variable" in a method definition
    # the arguments are the values you pass at function call
    # (you define the parameters, you make the arguments)
    params = signatures[node.fname].parameters
    assert len(node.args) == len(params)
    call_stash_updates = tuple(source.Update(source.ExprVar(param.typ, CallArgVarName(param.name + '/call-arg')), arg)
                               for param, arg in zip(params, node.args))

    def f(var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[source.ProgVarName | nip.GuardVarName]:
        # this will change with the new way of writing specs
        if not var.name.endswith('/arg'):
            assert False, f"unknown variable {var.name}"

        return call_arg_var_name(var)

    for i, pred in enumerate(func.cfg.all_preds[node_name], start=1):
        yield Insertion(after=pred,
                        before=node_name,
                        node_name=source.NodeName(
                            f'call_stash_{node_name}_pred_{i}'),
                        mk_node=lambda succ: source.NodeBasic(ProvenanceCallStash(), call_stash_updates, succ))

        precond = source.convert_expr_vars(
            f, signatures[node.fname].precondition)
        yield Insertion(after=pred,
                        before=node_name,
                        node_name=source.NodeName(
                            f'call_pre_{node_name}_pred_{i}'),
                        mk_node=lambda succ: NodePrecondObligationFnCall(ProvenancePreCondFnObligation(), precond, succ))

    rets = node.rets  # pyright isn't smart enough

    def g(var: source.ExprVarT[source.ProgVarName | nip.GuardVarName]) -> source.ExprVarT[source.ProgVarName | nip.GuardVarName]:
        if isinstance(var.name, source.CRetSpecialVar):
            assert 0 <= var.name.field_num and var.name.field_num <= len(
                rets) - NUM_GHOST_VARIABLES_CPARSER_FUNCTION_CALL
            return rets[var.name.field_num]
        elif var.name.endswith("/arg"):
            return call_arg_var_name(var)
        return var

    postcond = source.convert_expr_vars(
        g, signatures[node.fname].postcondition)
    yield Insertion(after=node_name,
                    before=node.succ,
                    node_name=source.NodeName(f'call_post_{node_name}'),
                    mk_node=lambda succ: NodeAssumePostCondFnCall(
                        ProvenancePostCondFnAssume(),
                        postcond,
                        succ))


def sprinkle_function_call_pre_and_post_conditions(func: nip.Function,
                                                   signatures: Mapping[str, TemporaryFunctionSignature]) -> Iterable[Insertion]:
    for node_name in func.traverse_topologically(skip_err_and_ret=True):
        node = func.nodes[node_name]
        if isinstance(node, source.NodeCall):
            yield from sprinkle_function_call_pre_and_post_condition(func, node_name, node, signatures)


@dataclass(frozen=True, slots=True)
class TemporaryFunctionSignature:
    """ These function signatures should be all loaded at the start,
        and then passed through each functions.

        At load time, we should make sure that the precondition and the post
        condition only talk about the variables they are allowed to talk
        about.

        TODO: make this temporary function signature the new
        FunctionSignature
    """
    parameters: Tuple[source.ExprVarT[source.ProgVarName], ...]
    returns: Tuple[source.ExprVarT[source.ProgVarName], ...]

    precondition: source.ExprT[source.ProgVarName | nip.GuardVarName]
    postcondition: source.ExprT[source.ProgVarName | nip.GuardVarName]


def sprinkle_ghost_code(filename: str, func: nip.Function, unsafe_ctx: Mapping[str, syntax.Function]) -> Function:
    ctx: dict[str, TemporaryFunctionSignature] = {}
    for fname, syn_func in unsafe_ctx.items():
        sig = source.convert_function_metadata(syn_func)
        ghost = ghost_data.get(filename, fname)

        precondition: source.ExprT[source.ProgVarName | nip.GuardVarName]
        postcondition: source.ExprT[source.ProgVarName | nip.GuardVarName]
        if ghost is None:
            precondition = source.expr_true
            postcondition = source.expr_true
        else:
            precondition = ghost.precondition
            postcondition = ghost.postcondition

        ctx[fname] = TemporaryFunctionSignature(parameters=sig.parameters,
                                                returns=sig.returns,
                                                precondition=precondition,
                                                postcondition=postcondition)

    insertions: list[Insertion] = []
    insertions.extend(sprinkle_subject_pre_and_post_conditions(func))
    insertions.extend(
        sprinkle_function_call_pre_and_post_conditions(func, ctx))
    insertions.extend(sprinkle_loop_invariants(func))

    new_nodes = apply_insertions(func, insertions)
    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    return Function(name=func.name, variables=func.variables ,nodes=new_nodes, cfg=cfg, loops=loops, ghost=func.ghost, signature=func.signature)
