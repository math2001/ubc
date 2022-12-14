from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, unique
from typing import Callable, Collection, Generic, Iterator, Mapping, NewType, Sequence, Set, TypeAlias, TypeVar
from typing_extensions import assert_never

import syntax
import abc_cfg

ProgVarName = NewType('ProgVarName', str)
VarNameKind = TypeVar("VarNameKind")

NodeName = NewType('NodeName', str)
NodeNameErr = NodeName('Err')
NodeNameRet = NodeName('Ret')


@dataclass(frozen=True)
class TypeStruct:
    name: str


@dataclass(frozen=True)
class TypeBitVec:
    """ Synonym for TypeWord
    """
    size: int


@dataclass(frozen=True)
class TypeArray:
    element_typ: Type
    size: int


@dataclass(frozen=True)
class TypePtr:
    pointee_type: Type


@dataclass(frozen=True)
class TypeFloatingPoint:
    exp_bits: int
    """ number of bits in the exponent """
    sig_bits: int
    """ number of bits in the significant """


@unique
class Builtin(Enum):
    BOOL = 'Bool'
    MEM = 'Mem'
    """ Memory """
    DOM = 'Dom'
    """ valid domain of memory operations """
    HTD = 'HTD'
    """ heap type description """
    PMS = 'PMS'
    """ phantom machine state """
    UNIT = 'UNIT'
    """ singleton type """
    TYPE = 'Type'
    """ type of Type expression used for pointer validity """
    TOKEN = 'Token'
    """ spec doesn't say what this is """
    ROUNDING_MODE = 'RoundingMode'


@dataclass(frozen=True)
class TypeBuiltin:
    builtin: Builtin


@dataclass(frozen=True)
class TypeWordArray:

    index_bits: int
    """ these are guesses from looking at the code, i don't actually know if
        that's what they're meant to represent

        number of bits used for the index?

        """

    value_bits: int
    """ number of bits used per value?
        same as for index_bits, i'm not actually sure
    """


Type = TypeStruct | TypeBitVec | TypePtr | TypeArray | TypeFloatingPoint | TypeBuiltin | TypeWordArray

type_bool = TypeBuiltin(Builtin.BOOL)
type_word8 = TypeBitVec(8)
type_word32 = TypeBitVec(32)
type_word64 = TypeBitVec(64)


def convert_type(typ: syntax.Type) -> Type:
    if typ.kind == 'Word':
        if typ.num == 8:
            return type_word8
        elif typ.num == 32:
            return type_word32
        elif typ.num == 64:
            return type_word64
        return TypeBitVec(typ.num)
    elif typ.kind == 'Ptr':
        assert typ.el_typ_symb is not None
        return TypePtr(typ.el_typ_symb)
    elif typ.kind == 'Array':
        assert typ.el_typ_symb is not None
        return TypeArray(typ.el_typ_symb, typ.num)
    elif typ.kind == 'FloatingPoint':
        return TypeFloatingPoint(typ.nums[0], typ.nums[1])
    elif typ.kind == 'Struct':
        return TypeStruct(typ.name)
    elif typ.kind == 'Builtin':
        return TypeBuiltin(Builtin(typ.name))
    elif typ.kind == 'WordArray':
        return TypeWordArray(typ.nums[0], typ.nums[1])
    raise NotImplementedError(f"Type {typ.kind} not implemented")


@dataclass(frozen=True)
class ABCExpr(Generic[VarNameKind]):
    typ: Type


@dataclass(frozen=True, order=True)
class ExprVar(ABCExpr[VarNameKind]):
    name: VarNameKind


@dataclass(frozen=True)
class ExprNum(ABCExpr):
    num: int


@dataclass(frozen=True)
class ExprType(ABCExpr):
    """ should have typ builtin.Type
    """
    val: Type


@dataclass(frozen=True)
class ExprSymbol(ABCExpr):
    name: str


@unique
class Operator(Enum):
    """ To convert graph lang operator name to this enum, just do Operator(parsed_operator_name)

    Some operators that are specified in the spec aren't used.
    Some operators that are used aren't specified in the spec.
    """
    PLUS = 'Plus'
    MINUS = 'Minus'
    TIMES = 'Times'
    MODULUS = 'Modulus'
    DIVIDED_BY = 'DividedBy'

    BW_AND = 'BWAnd'
    BW_OR = 'BWOr'
    BW_XOR = 'BWXor'

    SHIFT_LEFT = 'ShiftLeft'
    SHIFT_RIGHT = 'ShiftRight'
    SIGNED_SHIFT_RIGHT = 'SignedShiftRight'

    AND = 'And'
    OR = 'Or'
    IMPLIES = 'Implies'

    NOT = 'Not'

    TRUE = 'True'
    FALSE = 'False'

    EQUALS = 'Equals'
    LESS = 'Less'
    LESS_EQUALS = 'LessEquals'
    SIGNED_LESS = 'SignedLess'
    SIGNED_LESS_EQUALS = 'SignedLessEquals'

    BW_NOT = 'BWNot'
    WORD_REVERSE = 'WordReverse'
    WORD_CAST = 'WordCast'
    WORD_CAST_SIGNED = 'WordCastSigned'

    MEM_ACC = 'MemAcc'
    MEM_UPDATE = 'MemUpdate'

    WORD_ARRAY_ACCESS = 'WordArrayAccess'
    WORD_ARRAY_UPDATE = 'WordArrayUpdate'

    P_VALID = 'PValid'
    P_WEAK_VALID = 'PWeakValid'
    P_ALIGN_VALID = 'PAlignValid'
    P_GLOBAL_VALID = 'PGlobalValid'
    P_ARRAY_VALID = 'PArrayValid'

    MEM_DOM = 'MemDom'
    HTD_UPDATE = 'HTDUpdate'
    IF_THEN_ELSE = 'IfThenElse'

    # COUNT_LEADING_ZEROES = 'CountLeadingZeros'
    # COUNT_TRAILING_ZEROES = 'CountTrailingZeroes'

    # ROUND_NEAREST_TIES_TO_EVEN = 'roundNearestTiesToEven'
    # ROUND_NEAREST_TIES_TO_AWAY = 'roundNearestTiesToAway'
    # ROUND_TOWARD_POSITIVE = 'roundTowardPositive'
    # ROUND_TOWARD_NEGATIVE = 'roundTowardNegative'
    # ROUND_TOWARD_ZERO = 'roundTowardZero'

    # optional apparently
    # FP_ABS = 'fp.abs'
    # FP_NEG = 'fp.neg'
    # FP_ADD = 'fp.add'
    # FP_SUB = 'fp.sub'
    # FP_MUL = 'fp.mul'
    # FP_DIV = 'fp.div'
    # FP_FMA = 'fp.fma'
    # FP_SQRT = 'fp.sqrt'
    # FP_REM = 'fp.rem'
    # FP_ROUND_TO_INTEGRAL = 'fp.roundToIntegral'
    # FP_MIN = 'fp.min'
    # FP_MAX = 'fp.max'
    # FP_LEQ = 'fp.leq'
    # FP_LT = 'fp.lt'
    # FP_GEQ = 'fp.geq'
    # FP_GT = 'fp.gt'
    # FP_EQ = 'fp.eq'
    # FP_IS_NORMAL = 'fp.isNormal'
    # FP_IS_SUBNORMAL = 'fp.IsSubnormal'
    # FP_IS_ZERO = 'fp.isZero'
    # FP_IS_INFINITE = 'fp.isInfinite'
    # FP_IS_NAN = 'fp.isNaN'
    # FP_IS_NEGATIVE = 'fp.isNegative'
    # FP_IS_POSITIVE = 'fp.isPositive'

    # TO_FLOATING_POINT = 'ToFloatingPoint'
    # TO_FLOATING_POINT_SIGNED = 'ToFloatingPointSigned'
    # TO_FLOATING_POINT_UNSIGNED = 'ToFloatingPointUnsigned'
    # FLOATING_POINT_CAST = 'FloatingPointCast'


# operators that take no arguments
nulary_operators = {Operator.TRUE, Operator.FALSE}

pretty_binary_operators_ascii = {
    Operator.PLUS: '+',
    Operator.MINUS: '-',

    Operator.TIMES: '*',
    Operator.MODULUS: '%',
    Operator.DIVIDED_BY: '/',

    Operator.BW_AND: '&',
    Operator.BW_OR: '|',
    Operator.BW_XOR: '^',

    Operator.SHIFT_LEFT: '<<',
    Operator.SHIFT_RIGHT: '>>',
    Operator.SIGNED_SHIFT_RIGHT: '>>s',

    Operator.AND: '&&',
    Operator.OR: '||',
    Operator.IMPLIES: '->',

    Operator.EQUALS: '=',
    Operator.LESS: '<',
    Operator.LESS_EQUALS: '<=',
    Operator.SIGNED_LESS: '<s',
    Operator.SIGNED_LESS_EQUALS: '<=s',
}


@dataclass(frozen=True)
class ExprOp(ABCExpr[VarNameKind]):
    operator: Operator
    operands: Sequence[Expr[VarNameKind]]


Expr = ExprVar[VarNameKind] | ExprNum | ExprType | ExprOp[VarNameKind] | ExprSymbol
ProgVar: TypeAlias = ExprVar[ProgVarName]

expr_true: Expr = ExprOp(type_bool, Operator.TRUE, ())
expr_false: Expr = ExprOp(type_bool, Operator.FALSE, ())


def visit_expr(expr: Expr, visitor: Callable[[Expr], None]):
    visitor(expr)
    if isinstance(expr, ExprOp):
        for operand in expr.operands:
            visit_expr(operand, visitor)
    elif not isinstance(expr, ExprVar | ExprNum | ExprType | ExprSymbol):
        assert_never(expr)


def expr_where_vars_are_used_in_node(node: Node, selection: Set[ExprVar[VarNameKind]]) -> Iterator[tuple[ExprVar[VarNameKind], Expr[VarNameKind]]]:
    if isinstance(node, NodeBasic):
        for upd in node.upds:
            for var in selection & all_vars_in_expr(upd.expr):
                yield var, upd.expr
    elif isinstance(node, NodeCall):
        for arg in node.args:
            for var in selection & all_vars_in_expr(arg):
                yield var, arg
    elif isinstance(node, NodeCond):
        for var in selection & all_vars_in_expr(node.expr):
            yield var, node.expr
    elif not isinstance(node, NodeEmpty):
        assert_never(node)


def pretty_expr_ascii(expr: Expr) -> str:
    if isinstance(expr, ExprNum):
        return str(expr.num)
    elif isinstance(expr, ExprSymbol):
        return expr.name
    elif isinstance(expr, ExprType):
        return str(expr.val)
    elif isinstance(expr, ExprVar):
        return expr.name
    elif isinstance(expr, ExprOp):
        if expr.operator in pretty_binary_operators_ascii:
            assert len(expr.operands) == 2
            return f'({pretty_expr_ascii(expr.operands[0])} {pretty_binary_operators_ascii[expr.operator]} {pretty_expr_ascii(expr.operands[1])})'
        elif expr.operator == Operator.IF_THEN_ELSE:
            assert len(expr.operands) == 3
            cond, then, otherwise = (pretty_expr_ascii(operand)
                                     for operand in expr.operands)
            return f'({cond} ? {then} : {otherwise})'
        else:
            return f'{expr.operator.value}({", ".join(pretty_expr_ascii(operand) for operand in expr.operands)})'


def convert_expr(expr: syntax.Expr) -> Expr[ProgVarName]:
    typ = convert_type(expr.typ)
    if expr.kind == 'Op':
        return ExprOp(typ, Operator(expr.name), tuple(convert_expr(operand) for operand in expr.vals))
    elif expr.kind == 'Var':
        return ExprVar(typ, ProgVarName(expr.name))
    elif expr.kind == 'Num':
        return ExprNum(typ, expr.val)
    elif expr.kind == 'Type':
        return ExprType(typ, convert_type(expr.val))
    elif expr.kind == 'Symbol':
        return ExprSymbol(typ, expr.name)
    raise NotImplementedError


def all_vars_in_expr(expr: Expr[VarNameKind]) -> set[ExprVar[VarNameKind]]:
    s: set[ExprVar[VarNameKind]] = set()

    def visitor(expr: Expr):
        if isinstance(expr, ExprVar):
            s.add(ExprVar(expr.typ, expr.name))
    visit_expr(expr, visitor)
    return s


def expr_negate(expr: Expr[VarNameKind]) -> Expr[VarNameKind]:
    assert expr.typ == type_bool
    return ExprOp(type_bool, Operator.NOT, (expr, ))


def expr_or(lhs: Expr[VarNameKind], rhs: Expr[VarNameKind]) -> Expr[VarNameKind]:
    assert lhs.typ == type_bool
    assert rhs.typ == type_bool
    return ExprOp(type_bool, Operator.OR, (lhs, rhs))


def expr_and(lhs: Expr[VarNameKind], rhs: Expr[VarNameKind]) -> Expr[VarNameKind]:
    assert lhs.typ == type_bool
    assert rhs.typ == type_bool
    return ExprOp(type_bool, Operator.AND, (lhs, rhs))


def expr_implies(antecedent: Expr[VarNameKind], consequent: Expr[VarNameKind]) -> Expr[VarNameKind]:
    assert antecedent.typ == type_bool
    assert consequent.typ == type_bool
    return ExprOp(type_bool, Operator.IMPLIES, (antecedent, consequent))


# for the following commented out expr classes
# not present in the kernel functions, I don't want to make an abstraction for
# something i can't even test once

# @dataclass(frozen=True)
# class ExprField(Expr[VarNameKind]):
#     struct: Expr[VarNameKind]
#     field_name: str
#     field_type: Type

# @dataclass(frozen=True)
# class ExprFieldUpd(Expr[VarNameKind]):
#     struct: Expr[VarNameKind]
#     field_name: str
#     field_type: Type
#     val: Expr[VarNameKind]

#
# @dataclass(frozen=True)
# class ExprStructCons(Expr[VarNameKind]):
#     inits: Mapping[]


@dataclass(frozen=True)
class Update(Generic[VarNameKind]):
    var: ExprVar[VarNameKind]
    expr: Expr[VarNameKind]


@dataclass(frozen=True)
class NodeEmpty:
    succ: NodeName


@dataclass(frozen=True)
class NodeBasic(Generic[VarNameKind]):
    upds: tuple[Update[VarNameKind], ...]
    succ: NodeName


@dataclass(frozen=True)
class NodeCall(Generic[VarNameKind]):
    succ: NodeName
    fname: str
    args: tuple[Expr[VarNameKind], ...]
    rets: tuple[ExprVar[VarNameKind], ...]


@dataclass(frozen=True)
class NodeCond(Generic[VarNameKind]):
    expr: Expr[VarNameKind]  # TODO: Expr will take a VarNameKind
    succ_then: NodeName
    succ_else: NodeName


Node = NodeBasic[VarNameKind] | NodeCall[VarNameKind] | NodeCond[VarNameKind] | NodeEmpty

LoopHeaderName = NewType('LoopHeaderName', NodeName)


@dataclass(frozen=True)
class Loop(Generic[VarNameKind]):
    back_edge: tuple[NodeName, NodeName]
    """
    back_edge = (latch, loop header)
    """

    nodes: tuple[NodeName, ...]
    """ nodes forming a natural loop """

    targets: Collection[ExprVar[VarNameKind]]
    """ All the variables that are written to during the loop
    """

    @property
    def header(self) -> NodeName:
        return self.back_edge[1]


@dataclass(frozen=True)
class Function(Generic[VarNameKind]):

    name: str

    cfg: abc_cfg.CFG

    # TODO: find good way to freeze dict and keep type hints
    nodes: Mapping[NodeName, Node[VarNameKind]]
    """
    Node name => Node
    """

    loops: Mapping[LoopHeaderName, Loop[VarNameKind]]
    """
    loop header => loop information
    """

    arguments: tuple[ExprVar[VarNameKind], ...]

    def is_loop_header(self, node_name: NodeName) -> LoopHeaderName | None:
        if node_name in self.loops:
            return LoopHeaderName(node_name)
        return None

    def acyclic_preds_of(self, node_name: NodeName) -> Iterator[NodeName]:
        """ returns all the direct predecessors, removing the ones that would follow back edges """
        return (p for p in self.cfg.all_preds[node_name] if (p, node_name) not in self.cfg.back_edges)

    def traverse_topologically_bottom_up(self: Function) -> Iterator[NodeName]:
        q: list[NodeName] = [n for n, succs in self.cfg.all_succs.items() if len(
            [succ for succ in succs if (n, succ) not in self.cfg.back_edges]) == 0]
        visited: set[NodeName] = set()

        while q:
            n = q.pop(-1)
            if n in visited:
                continue

            if any(succ not in visited for succ in self.cfg.all_succs[n] if (n, succ) not in self.cfg.back_edges):
                continue

            visited.add(n)
            yield n

            for pred in self.cfg.all_preds[n]:
                if (pred, n) not in self.cfg.back_edges:
                    q.append(pred)

        assert len(visited - {NodeNameErr, NodeNameRet}
                   ) == len(self.nodes), visited

    def traverse_topologically(self: Function[VarNameKind]) -> Iterator[NodeName]:
        q: list[NodeName] = [
            n for n, preds in self.cfg.all_preds.items() if len([p for p in self.acyclic_preds_of(n)]) == 0]
        visited: set[NodeName] = set()
        while q:
            n = q.pop(-1)
            if n in visited:
                continue

            if not all(p in visited for p in self.acyclic_preds_of(n)):
                continue

            visited.add(n)
            yield n

            for succ in self.cfg.all_succs[n]:
                if (n, succ) not in self.cfg.back_edges:
                    q.append(succ)

        assert len(visited - {NodeNameErr, NodeNameRet}) == len(self.nodes)


def used_variables_in_node(node: Node[VarNameKind]) -> Set[ExprVar[VarNameKind]]:
    used_variables: set[ExprVar[VarNameKind]] = set()
    if isinstance(node, NodeBasic):
        for upd in node.upds:
            used_variables |= all_vars_in_expr(upd.expr)
    elif isinstance(node, NodeCall):
        for arg in node.args:
            used_variables |= all_vars_in_expr(arg)
    elif isinstance(node, NodeCond):
        used_variables |= all_vars_in_expr(node.expr)
    elif not isinstance(node, NodeEmpty):
        assert_never(node)
    return used_variables


def assigned_variables_in_node(func: Function[VarNameKind], n: NodeName) -> Set[ExprVar[VarNameKind]]:
    if n in (NodeNameRet, NodeNameErr):
        return set()

    assigned_variables: set[ExprVar[VarNameKind]] = set()
    node = func.nodes[n]
    if isinstance(node, NodeBasic):
        assigned_variables.update(upd.var for upd in node.upds)
    elif isinstance(node, NodeCall):
        assigned_variables.update(ret for ret in node.rets)
    elif not isinstance(node, NodeEmpty | NodeCond):
        assert_never(node)

    if loop_header := func.is_loop_header(n):
        assigned_variables.update(func.loops[loop_header].targets)

    return assigned_variables


def convert_function_nodes(nodes: Mapping[str | int, syntax.Node]) -> Mapping[NodeName, Node[ProgVarName]]:
    safe_nodes: dict[NodeName, Node[ProgVarName]] = {}
    for name, node in nodes.items():
        name = NodeName(str(name))
        if node.kind == "Basic":
            if len(node.upds) == 0:
                safe_nodes[name] = NodeEmpty(succ=NodeName(str(node.cont)))
            else:
                upds: list[Update] = []
                for var, expr in node.upds:
                    upds.append(Update(
                        var=ExprVar[ProgVarName](
                            convert_type(var[1]), ProgVarName(var[0])),
                        expr=convert_expr(expr)))
                safe_nodes[name] = NodeBasic(upds=tuple(
                    upds), succ=NodeName(str(node.cont)))
        elif node.kind == "Call":
            node.args
            safe_nodes[name] = NodeCall(
                succ=NodeName(str(node.cont)),
                fname=node.fname,
                args=tuple(convert_expr(arg) for arg in node.args),
                rets=tuple(ExprVar(convert_type(typ), ProgVarName(name)) for name, typ in node.rets))
        elif node.kind == "Cond":
            safe_nodes[name] = NodeCond(
                succ_then=NodeName(str(node.left)), succ_else=NodeName(str(node.right)), expr=convert_expr(node.cond))
        else:
            raise ValueError(f"unknown kind {node.kind!r}")
    return safe_nodes


def convert_function(func: syntax.Function):
    safe_nodes = convert_function_nodes(func.nodes)
    all_succs = abc_cfg.compute_all_successors_from_nodes(safe_nodes)
    assert func.entry is not None
    cfg = abc_cfg.compute_cfg_from_all_succs(
        all_succs, NodeName(str(func.entry)))
    loops = abc_cfg.compute_loops(safe_nodes, cfg)

    args = tuple(ExprVar(convert_type(typ), ProgVarName(name))
                 for name, typ in func.inputs)

    return Function(cfg=cfg, nodes=safe_nodes, loops=loops, arguments=args, name=func.name)
