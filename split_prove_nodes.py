""" Used to understand why a proof doesn't go through.

It splits a prove node (a and b and c) into multiple prove nodes so that it is
easier to figure out which assertion failed.

It's not enabled by default.
"""

import source
import abc_cfg
import nip
import ghost_code


def split_prove_nodes(func: ghost_code.Function) -> ghost_code.Function:
    """ splits prove nodes where the expression is a conjunction of n terms into n prove nodes
    """

    new_nodes: dict[source.NodeName,
                    source.Node[source.ProgVarName | nip.GuardVarName]] = {}
    for node_name, node in func.nodes.items():
        is_prove_node = isinstance(
            node, source.NodeCond) and node.succ_else == source.NodeNameErr
        if not is_prove_node:
            new_nodes[node_name] = node
            continue

        assert isinstance(node, source.NodeCond)

        conjuncts = tuple(source.expr_split_conjuncts(node.expr))
        for i, conjunct in enumerate(conjuncts, start=1):
            if i == 1:
                new_node_name = node_name
            else:
                new_node_name = source.NodeName(f"{node_name}_conjunct_{i}")

            if i == len(conjuncts):
                succ = node.succ_then  # original successor
            else:
                succ = source.NodeName(f"{node_name}_conjunct_{i+1}")

            # we use type(node) instead of NodeCond because we might be using
            # a specific subtype (NodeLoopInvariantProofAssumption for
            # example).
            new_nodes[new_node_name] = type(node)(
                node.origin, conjunct, succ, source.NodeNameErr)

    all_succs = abc_cfg.compute_all_successors_from_nodes(new_nodes)
    cfg = abc_cfg.compute_cfg_from_all_succs(all_succs, func.cfg.entry)
    loops = abc_cfg.compute_loops(
        new_nodes, cfg)
    assert loops.keys() == func.loops.keys(
    ), "more work required: loop headers changed during conversion, need to keep ghost's loop invariant in sync"

    return ghost_code.Function(name=func.name,
                               variables=func.variables,
                               nodes=new_nodes,
                               cfg=cfg,
                               loops=loops,
                               ghost=func.ghost,
                               signature=func.signature)
