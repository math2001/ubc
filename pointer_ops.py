import nip
import source
from typing_extensions import assert_never


class GenericFunction(nip.GenericFunction[source.VarNameKind, source.VarNameKind2]):
    """
    Function pre conditions, post condition, and loop invariants inserted in
    the CFG
    """


Function = GenericFunction[source.ProgVarName |
                           nip.GuardVarName, source.ProgVarName | nip.GuardVarName]


def translate_expr_pointer_ops(expr: source.ExprT[source.ProgVarName | nip.GuardVarName]) -> source.ExprT[source.ProgVarName | nip.GuardVarName]:
    return NotImplemented


def translate_update_pointer_ops(upd: source.Update[source.ProgVarName | nip.GuardVarName]) -> source.Update[source.ProgVarName | nip.GuardVarName]:
    return NotImplemented


def translate_node_pointer_ops(node: source.Node) -> source.Node:
    if isinstance(node, source.NodeAssert):
        x = translate_expr_pointer_ops(node.expr)
        return source.NodeAssert(expr=x, succ=node.succ)
    elif isinstance(node, source.NodeBasic):
        upds = [translate_update_pointer_ops(upd) for upd in node.upds]
        return source.NodeBasic(tuple(upds), node.succ)
    elif isinstance(node, source.NodeEmpty):
        return node
    elif isinstance(node, source.NodeCall):
        pass
    elif isinstance(node, source.NodeAssume):
        pass
    elif isinstance(node, source.NodeCond):
        pass
    else:
        assert_never(node)
    return NotImplemented


def decompile(func: nip.Function) -> Function:
    """this stage replaces all pointer operations with expressions the later stages can deal with"""

    for name in func.traverse_topologically():
        node = func.nodes[name]

    return NotImplemented
