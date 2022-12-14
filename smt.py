from __future__ import annotations
from enum import Enum
import subprocess
from typing import TYPE_CHECKING, Iterator, Literal, Mapping, Sequence
from typing_extensions import NamedTuple, NewType, assert_never

import math
import textwrap
import assume_prove
import source
import re
from utils import open_temp_file

SMTLIB = NewType("SMTLIB", str)

ops_to_smt: Mapping[source.Operator, SMTLIB] = {
    source.Operator.PLUS: SMTLIB("bvadd"),
    source.Operator.MINUS: SMTLIB("bvsub"),
    source.Operator.TIMES: SMTLIB("bvmul"),
    source.Operator.MODULUS: SMTLIB("bvurem"),
    source.Operator.DIVIDED_BY: SMTLIB("bvudiv"),
    source.Operator.BW_AND: SMTLIB("bvand"),
    source.Operator.BW_OR: SMTLIB("bvor"),
    source.Operator.BW_XOR: SMTLIB("bvxor"),
    source.Operator.AND: SMTLIB("and"),
    source.Operator.OR: SMTLIB("or"),
    source.Operator.IMPLIES: SMTLIB("=>"),
    source.Operator.EQUALS: SMTLIB("="),
    source.Operator.LESS: SMTLIB("bvult"),
    source.Operator.LESS_EQUALS: SMTLIB("bvule"),
    source.Operator.SIGNED_LESS: SMTLIB("bvslt"),
    source.Operator.SIGNED_LESS_EQUALS: SMTLIB("bvsle"),
    source.Operator.SHIFT_LEFT: SMTLIB("bvshl"),
    source.Operator.SHIFT_RIGHT: SMTLIB("bvlshr"),
    source.Operator.SIGNED_SHIFT_RIGHT: SMTLIB("bvashr"),
    source.Operator.NOT: SMTLIB("not"),
    source.Operator.BW_NOT: SMTLIB("bvnot"),
    source.Operator.TRUE: SMTLIB("true"),
    source.Operator.FALSE: SMTLIB("false"),
    source.Operator.IF_THEN_ELSE: SMTLIB("ite"),
    source.Operator.WORD_ARRAY_ACCESS: SMTLIB("select"),
    source.Operator.WORD_ARRAY_UPDATE: SMTLIB("store"),
    source.Operator.MEM_DOM: SMTLIB("mem-dom"),
}

# 〈simple_symbol 〉 ::= a non-empty sequence of letters, digits and the characters
#                       + - / * = % ? ! . $ _ ~ & ˆ < > @ that does not start
#                       with a digit
RE_VALID_SMTLIB_SIMPLE_SYMBOL = re.compile(
    r'^[a-zA-Z+\-/*=%?!.$_~<>@][a-zA-Z+\-/*=%?!.$_~<>@0-9]+$')

Identifier = NewType('Identifier', str)


def identifier(illegal_name: assume_prove.APVarName) -> Identifier:
    # '#' are disallowed in SMT
    renamed = illegal_name.replace('#', '@')
    assert RE_VALID_SMTLIB_SIMPLE_SYMBOL.match(
        renamed), f"identifier {illegal_name!r} isn't valid"
    return Identifier(renamed)


class CmdDeclareFun(NamedTuple):
    symbol: Identifier
    arg_sorts: Sequence[source.Type]
    ret_sort: source.Type


class CmdAssert(NamedTuple):
    expr: source.Expr


class CmdCheckSat(NamedTuple):
    pass


Cmd = CmdDeclareFun | CmdAssert | CmdCheckSat


def smt_bitvec_of_size(val: int, size: int) -> SMTLIB:
    assert val >= 0
    assert size > 0
    return SMTLIB(f"(_ bv{val} {size})")


def smt_extract(msb_idx: int, lsb_idx: int, expected_num_bits: int, lhs: source.Expr[assume_prove.APVarName]) -> SMTLIB:
    """
    msb_idx: most significant bit index
    lsb_idx: least significant bit index
    expected_num_bits is just used for safety

    All function symbols with declaration of the form

        ((_ extract i j) (_ BitVec m) (_ BitVec n))

    where
    - i, j, m, n are numerals
    - m > i ≥ j ≥ 0,
    - n = i - j + 1
    """

    assert isinstance(lhs.typ, source.TypeBitVec)
    assert lhs.typ.size > msb_idx >= lsb_idx >= 0
    assert expected_num_bits == msb_idx - lsb_idx + 1

    return SMTLIB(f"((_ extract {msb_idx} {lsb_idx}) {emit_expr(lhs)})")


def smt_zero_extend(num_bits: int, lhs: source.Expr[assume_prove.APVarName]) -> SMTLIB:
    assert num_bits > 0
    return SMTLIB(f"((_ zero_extend {num_bits}) {emit_expr(lhs)})")


def smt_sign_extend(num_bits: int, lhs: source.Expr[assume_prove.APVarName]) -> SMTLIB:
    assert num_bits > 0
    return SMTLIB(f"((_ sign_extend {num_bits}) {emit_expr(lhs)})")


def emit_num_with_correct_type(expr: source.ExprNum) -> SMTLIB:
    if isinstance(expr.typ, source.TypeBitVec):
        assert - \
            2 ** expr.typ.size <= expr.num < 2 ** expr.typ.size, f"{expr.num=} doesn't fit in the type {expr.typ=}"
        if expr.num >= 0:
            num = expr.num
        else:
            num = 2 ** 32 + expr.num
        return smt_bitvec_of_size(val=num, size=expr.typ.size)
    assert False, f"{expr} not supported"


def emit_bitvec_cast(target_typ: source.TypeBitVec, operator: Literal[source.Operator.WORD_CAST, source.Operator.WORD_CAST_SIGNED], lhs: source.Expr[assume_prove.APVarName]) -> SMTLIB:
    assert isinstance(lhs.typ, source.TypeBitVec)
    if lhs.typ.size == target_typ.size:
        return emit_expr(lhs)

    if target_typ.size < lhs.typ.size:
        # extract the bottom <target_type.size> bits
        return smt_extract(msb_idx=target_typ.size - 1, lsb_idx=0, expected_num_bits=target_typ.size, lhs=lhs)

    assert lhs.typ.size < target_typ.size
    if operator == source.Operator.WORD_CAST:
        return smt_zero_extend(num_bits=target_typ.size, lhs=lhs)
    elif operator == source.Operator.WORD_CAST_SIGNED:
        return smt_sign_extend(num_bits=target_typ.size, lhs=lhs)

    assert_never(operator)


def emit_expr(expr: source.Expr[assume_prove.APVarName]) -> SMTLIB:
    if isinstance(expr, source.ExprNum):
        return emit_num_with_correct_type(expr)
    elif isinstance(expr, source.ExprOp):

        # mypy isn't smart enough to understand `in`, we split the iffs
        if expr.operator == source.Operator.WORD_CAST:
            assert len(expr.operands) == 1
            assert isinstance(expr.typ, source.TypeBitVec)
            return emit_bitvec_cast(expr.typ, source.Operator.WORD_CAST, expr.operands[0])

        if expr.operator == source.Operator.WORD_CAST_SIGNED:
            assert len(expr.operands) == 1
            assert isinstance(expr.typ, source.TypeBitVec)
            return emit_bitvec_cast(expr.typ, source.Operator.WORD_CAST_SIGNED, expr.operands[0])

        if expr.operator in source.nulary_operators:
            return SMTLIB(ops_to_smt[expr.operator])

        return SMTLIB(f'({ops_to_smt[expr.operator]} {" ".join(emit_expr(op) for op in expr.operands)})')
    elif isinstance(expr, source.ExprVar):
        return SMTLIB(f'{identifier(expr.name)}')
    elif isinstance(expr, source.ExprSymbol | source.ExprType):
        assert False, "what do i do with this?"

    assert_never(expr)


def emit_sort(typ: source.Type) -> SMTLIB:
    if isinstance(typ, source.TypeBuiltin):
        if typ.builtin == source.Builtin.BOOL:
            return SMTLIB('Bool')
    elif isinstance(typ, source.TypeBitVec):
        return SMTLIB(f'(_ BitVec {typ.size})')
    assert False, typ


def emit_cmd(cmd: Cmd) -> SMTLIB:
    if isinstance(cmd, CmdDeclareFun):
        arg_sorts = " ".join(emit_sort(s) for s in cmd.arg_sorts)
        ret_sort = emit_sort(cmd.ret_sort)
        return SMTLIB(f'(declare-fun {cmd.symbol} ({arg_sorts}) {ret_sort})')
    elif isinstance(cmd, CmdAssert):
        return SMTLIB(f"(assert {emit_expr(cmd.expr)})")
    elif isinstance(cmd, CmdCheckSat):
        return SMTLIB(f"(check-sat)")
    assert_never(cmd)


def cmd_assert_eq(name: assume_prove.APVarName, rhs: source.Expr[assume_prove.APVarName]):
    return CmdAssert(source.ExprOp(rhs.typ, source.Operator.EQUALS, (source.ExprVar(rhs.typ, name), rhs)))


def merge_smtlib(it: Iterator[SMTLIB]) -> SMTLIB:
    return SMTLIB('\n'.join(it))


def make_smtlib(p: assume_prove.AssumeProveProg) -> SMTLIB:
    emited_identifiers: set[Identifier] = set()
    emited_variables: set[assume_prove.APVarName] = set()

    # emit all auxilary variable declaration (declare-fun node_x_ok () Bool)
    cmds: list[Cmd] = []
    for node_ok_name in p.nodes_script:
        cmds.append(CmdDeclareFun(identifier(
            node_ok_name), (), source.type_bool))
        emited_identifiers.add(identifier(node_ok_name))
        emited_variables.add(node_ok_name)

    assert len(emited_identifiers) == len(
        emited_variables), "renaming variables to valid SMT LIB identifiers results in a name clash"

    # emit all variable declaration (declare-fun y () <sort>)
    for script in p.nodes_script.values():
        for ins in script:
            for var in source.all_vars_in_expr(ins.expr):
                iden = identifier(var.name)
                if iden not in emited_identifiers:
                    cmds.append(CmdDeclareFun(iden, (), var.typ))
                    emited_identifiers.add(iden)

    # emit all assertions from nodes (node_x_ok = wp(x))
    for node_ok_name, script in p.nodes_script.items():
        expr = assume_prove.apply_weakest_precondition(script)
        cmds.append(cmd_assert_eq(node_ok_name, expr))

    cmds.append(CmdAssert(source.expr_negate(
        source.ExprVar(source.type_bool, p.entry))))

    cmds.append(CmdCheckSat())
    return merge_smtlib(emit_cmd(cmd) for cmd in cmds)


class CheckSatResult(Enum):
    UNSAT = 'unsat'
    SAT = 'sat'


def send_smtlib_to_z3(smtlib: SMTLIB) -> Iterator[CheckSatResult]:
    """ Send command to an smt solver and returns a boolean per (check-sat)
    """

    # print("sending SMTLIB:")
    # for i, line in enumerate(emit_cmd(cmd) for cmd in cmds):
    #     print(f'{str(i+1).rjust(int(math.log10(len(cmds)) + 1))} | {line}')

    # p = subprocess.Popen(["z3", "-version"])
    # err = p.wait()
    # if err:
    #     raise ValueError("z3 not found")

    with open_temp_file(suffix='.smt2') as (f, fullpath):
        f.write(smtlib)
        f.close()

        p = subprocess.Popen(["z3", "-file:" + fullpath],
                             stderr=subprocess.PIPE, stdout=subprocess.PIPE)
        p.wait()

    assert p.stderr is not None
    assert p.stdout is not None

    if p.returncode != 0:
        print("stderr:")
        print(textwrap.indent(p.stdout.read().decode('utf-8'), '   '))
        print("Return code:", p.returncode)
        return

    lines = p.stdout.read().splitlines()
    for ln in lines:
        yield CheckSatResult(ln.decode('utf-8'))
