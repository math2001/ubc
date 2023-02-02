import dataclasses
from typing import Generic, Mapping, NewType, Set, TypeAlias, TypeVar
from typing_extensions import assert_never
import abc_cfg
import source
import nip
from utils import set_union
from dataclasses import dataclass


IncarnationNum = NewType('IncarnationNum', int)
IncarnationBase = IncarnationNum(1)

# Incarnation is immutable, so its generic parameter is covariant
BaseVarName = TypeVar('BaseVarName', source.ProgVarName,
                      nip.GuardVarName, covariant=True)


@dataclass(frozen=True)
class Incarnation(Generic[BaseVarName]):
    base: BaseVarName
    inc: IncarnationNum


BaseVar: TypeAlias = source.ExprVarT[BaseVarName]
Var: TypeAlias = source.ExprVarT[Incarnation[BaseVarName]]


@dataclass(frozen=True)
class Function(source.Function[Incarnation[source.ProgVarName | nip.GuardVarName]]):
    """ DSA Function """

    contexts: Mapping[source.NodeName,
                      Mapping[source.ProgVar | nip.GuardVar, IncarnationNum]]
    """ Mapping for each node from prog variable to the incarnation number at that node
    """


def unpack_dsa_var_name(v: Incarnation[BaseVarName]) -> tuple[BaseVarName, IncarnationNum]:
    return v.base, v.inc


def unpack_dsa_var(var: Var[BaseVarName]) -> tuple[source.ExprVarT[BaseVarName], IncarnationNum]:
    return source.ExprVar(var.typ, var.name.base), var.name.inc


def get_base_var(var: Var[BaseVarName]) -> BaseVar[BaseVarName]:
    return source.ExprVar(var.typ, var.name.base)


def make_dsa_var(v: BaseVar[BaseVarName], inc: IncarnationNum) -> Var[BaseVarName]:
    return source.ExprVar(v.typ, Incarnation(v.name, inc))


def guard_var_at_node(func: Function, n: source.NodeName, var: Var[source.ProgVarName]) -> Var[nip.GuardVarName]:
    guard_base_name = nip.guard_name(var.name.base)
    guard_base_var = source.ExprVar(source.type_bool, guard_base_name)
    incarnation: Incarnation[nip.GuardVarName] = Incarnation(
        guard_base_name, func.contexts[n][guard_base_var])
    return source.ExprVar(var.typ, incarnation)


@dataclasses.dataclass
class DSABuilder:
    original_func: source.Function[source.ProgVarName | nip.GuardVarName]

    dsa_nodes: dict[source.NodeName,
                    source.Node[Incarnation[nip.GuardVarName | source.ProgVarName]]]
    """
    Mutated during construction
    """

    incarnations: dict[source.NodeName,
                       Mapping[source.ProgVar, IncarnationNum]]
    """
    node_name => prog_var_name => set of incarnation numbers

    mutated during construction
    """

    insertions: dict[source.NodeName, Mapping[source.ProgVar, IncarnationNum]]
    """ Nodes to insert (join nodes)

    node_name => prog_var_name => incarnation number

    (there can only be one inserted incarnated number per node per var because
    otherwise we would merge the two together).

    Mutable during construction
    """


def compute_node_variable_dependencies(func: source.Function[source.ProgVarName]) -> Mapping[source.NodeName, Set[source.ProgVar]]:
    """
    For a given node name n, deps[n] gives the set of variables that are
    refered to in n or any of its (possibly indirect) successors.
    """
    deps: dict[source.NodeName, Set[source.ProgVar]] = {}
    for node_name in func.traverse_topologically_bottom_up():
        if node_name in (source.NodeNameErr, source.NodeNameRet):
            deps[node_name] = set()
            continue
        deps[node_name] = source.used_variables_in_node(func.nodes[node_name]).union(
            *(deps[succ] for succ in func.cfg.all_succs[node_name] if (node_name, succ) not in func.cfg.back_edges))

    return deps


def apply_incarnations(
        context: Mapping[source.ProgVar, IncarnationNum],
        root: source.ExprT[BaseVarName]) -> source.ExprT[Incarnation[BaseVarName]]:
    """ applies incarnation, but if a variable isn't defined in the context, it silently uses base as the incarnation count.
    """

    if isinstance(root, source.ExprNum | source.ExprType | source.ExprSymbol):
        return root
        # return cast(source.ExprT[VarName], root)
    elif isinstance(root, source.ExprVar):
        var: source.ProgVar = source.ExprVar(root.typ, root.name)

        if var not in context:
            # the variable wasn't defined in *any* predecessor
            # however, this might be fine, for example:
            #
            # int a; if (0) return a + 1;
            incarnation_number = IncarnationBase
        else:
            incarnation_number = context[var]

        dsa_name = Incarnation(root.name, incarnation_number)
        return source.ExprVar(root.typ, name=dsa_name)
    elif isinstance(root, source.ExprOp):
        return source.ExprOp(root.typ, source.Operator(root.operator), operands=tuple(
            apply_incarnations(context, operand) for operand in root.operands
        ))
    elif isinstance(root, source.ExprFunction):
        assert False, "there shouldn't be any function in the graph lang"
    assert_never(root)


def get_next_dsa_var_incarnation_number(s: DSABuilder, current_node: source.NodeName, var: source.ProgVar) -> IncarnationNum:
    max_inc_num: IncarnationNum | None = None
    if current_node in s.insertions and var in s.insertions[current_node]:
        max_inc_num = s.insertions[current_node][var]

    for pred_name in s.original_func.acyclic_preds_of(current_node):
        if var not in s.incarnations[pred_name]:
            continue
        if max_inc_num is None or s.incarnations[pred_name][var] > max_inc_num:
            max_inc_num = s.incarnations[pred_name][var]

    if not max_inc_num:
        return IncarnationBase

    return IncarnationNum(max_inc_num + IncarnationNum(1))


def get_next_dsa_var_incarnation_number_from_context(s: DSABuilder, context: Mapping[source.ProgVar, IncarnationNum], var: source.ProgVar) -> IncarnationNum:
    if var in context:
        return IncarnationNum(context[var] + IncarnationNum(1))
    return IncarnationBase


def apply_insertions(s: DSABuilder) -> None:
    prog_var_deps = compute_node_variable_dependencies(s.original_func)

    j = 0
    for node_name, node_insertions in s.insertions.items():
        for pred_name in s.original_func.acyclic_preds_of(node_name):

            updates: list[source.Update[Incarnation[source.ProgVarName | nip.GuardVarName]]] = [
            ]
            for prog_var, new_incarnation_number in node_insertions.items():
                # some variables might not be defined on all paths and still
                # represent legal code
                # good examples: dsa.txt@fail_arr_undefined_behaviour
                #                dsa.txt@shift_diag  (look at the ret variable)
                if prog_var not in s.incarnations[pred_name]:
                    continue

                # the successors don't need this variable, so don't emit a
                # joiner
                if prog_var not in prog_var_deps[node_name]:
                    continue

                old_incarnation_number = s.incarnations[pred_name][prog_var]

                updates.append(source.Update(make_dsa_var(prog_var, new_incarnation_number),
                                             source.ExprVar(prog_var.typ, name=Incarnation(prog_var.name, old_incarnation_number))))
            if len(updates) == 0:
                continue

            j += 1
            join_node_name = source.NodeName(f'j{j}')
            pred = s.dsa_nodes[pred_name]
            if isinstance(pred, source.NodeCond):
                assert node_name in (pred.succ_then, pred.succ_else)
                if node_name == pred.succ_then:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_then=join_node_name)
                else:
                    s.dsa_nodes[pred_name] = dataclasses.replace(
                        pred, succ_else=join_node_name)
            elif isinstance(pred, source.NodeBasic | source.NodeEmpty | source.NodeCall):
                # carefull, type hints for dataclasses.replace are too
                # permissive right now
                s.dsa_nodes[pred_name] = dataclasses.replace(
                    pred, succ=join_node_name)
            else:
                assert_never(pred)

            assert len(updates) > 0, f"{node_insertions=}"
            join_node = source.NodeBasic(tuple(updates), node_name)
            s.dsa_nodes[join_node_name] = join_node


def recompute_loops_post_dsa(s: DSABuilder, dsa_loop_targets: Mapping[source.LoopHeaderName, tuple[Var[BaseVarName], ...]], new_cfg: abc_cfg.CFG) -> Mapping[source.LoopHeaderName, source.Loop[Incarnation[BaseVarName]]]:
    abc_cfg.assert_single_loop_header_per_loop(new_cfg)

    # loop header => loop nodes
    all_loop_nodes: dict[source.LoopHeaderName,
                         tuple[source.NodeName, ...]] = {}
    for back_edge in new_cfg.back_edges:
        _, loop_header = back_edge
        loop_nodes = abc_cfg.compute_natural_loop(new_cfg, back_edge)

        assert all(loop_header in new_cfg.all_doms[n]
                   for n in loop_nodes), "the loop header should dominate all the nodes in the loop body"

        all_loop_nodes[source.LoopHeaderName(loop_header)] = loop_nodes

    assert all_loop_nodes.keys() == s.original_func.loops.keys(
    ), "loop headers should remain the same through DSA transformation"

    loops: dict[source.LoopHeaderName,
                source.Loop[Incarnation[BaseVarName]]] = {}
    for loop_header, loop_nodes in all_loop_nodes.items():
        assert set(s.original_func.loops[loop_header].nodes).issubset(
            loop_nodes), "dsa only inserts joiner nodes, all previous loop nodes should still be loop nodes"
        loops[loop_header] = source.Loop(back_edge=s.original_func.loops[loop_header].back_edge,
                                         targets=dsa_loop_targets[loop_header],
                                         nodes=loop_nodes)
    return loops


X = source.ProgVarName | nip.GuardVarName


def dsa(func: source.Function[X]) -> Function:
    """
    Returns the dsa function, and an artifact to make it easy to emit
    expressions into the DSA later on (used to emit the loop invariants)
    """

    # for each node, for each prog variable, keep a set of possible dsa incarnations
    # (this is going to use a lot of memory but oh well)
    #
    # when getting the latest incarnation, lookup it in the insertions for the
    # current node. If there, return the incarnation. Otherwise, look in the
    # predecessors. If they all return the same incarnation, return that.
    # Otherwise,
    #   - fresh_var = (prog_var_name, max(inc num) + 1)
    #   - record an insertion (current node, prog_var_name, fresh_var)
    #   - return fresh_var
    #
    # at the end, apply the insertions
    # recompute cfg

    s = DSABuilder(original_func=func, insertions={},
                   dsa_nodes={}, incarnations={})

    entry_incarnations: dict[source.ExprVarT[source.ProgVarName |
                                             nip.GuardVarName], IncarnationNum] = {}
    dsa_args: list[source.ExprVarT[Incarnation[source.ProgVarName |
                                               nip.GuardVarName]]] = []
    for arg in func.arguments:
        dsa_args.append(make_dsa_var(arg, IncarnationBase))
        entry_incarnations[arg] = IncarnationBase

    assert len(set(unpack_dsa_var_name(arg.name)[0] for arg in dsa_args)) == len(
        dsa_args), "unexpected duplicate argument name"

    dsa_loop_targets: dict[source.LoopHeaderName,
                           tuple[Var[source.ProgVarName | nip.GuardVarName], ...]] = {}
    for current_node in func.traverse_topologically():

        if current_node in (source.NodeNameErr, source.NodeNameRet):
            continue

        # build up a context (map from prog var to incarnation numbers)
        # TODO: clean this up
        context: dict[BaseVar[source.ProgVarName |
                              nip.GuardVarName], IncarnationNum]
        curr_node_insertions: dict[BaseVar[source.ProgVarName | nip.GuardVarName],
                                   IncarnationNum] | None = None
        if current_node == func.cfg.entry:
            context = entry_incarnations
        else:
            context = {}
            curr_node_insertions = {}

            all_variables: set[BaseVar[source.ProgVarName | nip.GuardVarName]] = set_union(set(s.incarnations[p].keys(
            )) for p in s.original_func.acyclic_preds_of(current_node))

            for var in all_variables:
                possibilities = set(s.incarnations[p][var] for p in s.original_func.acyclic_preds_of(
                    current_node) if var in s.incarnations[p])

                if len(possibilities) > 1:
                    # predecessors disagree about predecessors, we need to insert a join node
                    fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                        s, current_node, var)
                    curr_node_insertions[var] = fresh_incarnation_number
                    context[var] = fresh_incarnation_number
                elif len(possibilities) == 1:
                    context[var] = next(iter(possibilities))
                else:
                    assert False, "I didn't think this case was possible"

            if curr_node_insertions:
                # we need to insert some join nodes
                s.insertions[current_node] = curr_node_insertions

        if loop_header := func.is_loop_header(current_node):
            targets: list[Var[source.ProgVarName | nip.GuardVarName]] = []

            for target in func.loops[loop_header].targets:
                # havoc the loop targets
                fresh_incarnation_number = get_next_dsa_var_incarnation_number(
                    s, current_node, target)
                context[target] = fresh_incarnation_number
                targets.append(make_dsa_var(
                    target, fresh_incarnation_number))

            dsa_loop_targets[loop_header] = tuple(targets)

        added_incarnations: dict[BaseVar[source.ProgVarName |
                                         nip.GuardVarName], Var[source.ProgVarName | nip.GuardVarName]] = {}

        # print(f'{current_node=}')
        # print(f'{curr_node_insertions=}')
        # for var in context:
        #     print(
        #         f'  {var.name}', context[var], '  [joiner]' if curr_node_insertions and var in curr_node_insertions else '')

        node = func.nodes[current_node]
        if isinstance(node, source.NodeBasic):
            upds: list[source.Update[Incarnation[source.ProgVarName |
                                                 nip.GuardVarName]]] = []
            for upd in node.upds:
                # notice that we don't take into consideration the previous
                # updates from the same node. That's because the updates are
                # simultaneous.
                expr = apply_incarnations(context, upd.expr)
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, upd.var)
                dsa_var = make_dsa_var(upd.var, inc)
                upds.append(source.Update(dsa_var, expr))
                assert upd.var not in added_incarnations, "duplicate updates in BasicNode"
                added_incarnations[upd.var] = dsa_var

            s.dsa_nodes[current_node] = source.NodeBasic(
                tuple(upds), succ=node.succ)
        elif isinstance(node, source.NodeCond):
            s.dsa_nodes[current_node] = source.NodeCond(
                expr=apply_incarnations(context, node.expr),
                succ_then=node.succ_then,
                succ_else=node.succ_else,
            )
        elif isinstance(node, source.NodeCall):
            args = tuple(apply_incarnations(context, arg)
                         for arg in node.args)

            rets: list[Var[source.ProgVarName | nip.GuardVarName]] = []
            for ret in node.rets:
                inc = get_next_dsa_var_incarnation_number_from_context(
                    s, context, ret)
                rets.append(make_dsa_var(ret, inc))
                added_incarnations[ret] = rets[-1]

            s.dsa_nodes[current_node] = source.NodeCall(
                succ=node.succ,
                args=args,
                rets=tuple(rets),
                fname=node.fname,
            )
        elif isinstance(node, source.NodeEmpty):
            s.dsa_nodes[current_node] = node
        else:
            assert_never(node)

        # print("  + ")
        # for var, incs in added_incarnations.items():
        #     print(f'  {var.name}', incs.name[1])

        curr_node_incarnations = dict(context)
        for prog_var, dsa_var in added_incarnations.items():
            _, incarnation_number = unpack_dsa_var_name(dsa_var.name)
            curr_node_incarnations[prog_var] = incarnation_number
        s.incarnations[current_node] = curr_node_incarnations

    apply_insertions(s)

    # need to recompute the cfg from dsa_nodes
    all_succs = abc_cfg.compute_all_successors_from_nodes(s.dsa_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)

    # FIXME: this function is useless
    loops = recompute_loops_post_dsa(s, dsa_loop_targets, cfg)

    return Function(
        cfg=cfg,
        arguments=tuple(dsa_args),
        loops=loops,
        name=func.name,
        nodes=s.dsa_nodes,
        contexts=s.incarnations)
