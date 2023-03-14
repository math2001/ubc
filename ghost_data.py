from functools import reduce
import source

conj = source.expr_and
disj = source.expr_or
imp = source.expr_implies

udiv = source.expr_udiv
mul = source.expr_mul
plus = source.expr_plus
sub = source.expr_sub

slt = source.expr_slt
sle = source.expr_sle
eq = source.expr_eq
def neq(a, b): return source.expr_negate(source.expr_eq(a, b))


T = source.expr_true
F = source.expr_false


def get(file_name: str, func_name: str) -> source.Ghost[source.HumanVarName] | None:
    if file_name.endswith('.c'):
        file_name = file_name[:-len('.c')] + '.txt'
    if file_name in universe and func_name in universe[file_name]:
        return universe[file_name][func_name]
    return None


def conjs(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    # pyright is stupid, but mypy works it out (we only care about mypy)
    return reduce(source.expr_and, xs)  # pyright: ignore


def i32(n: int) -> source.ExprNumT:
    assert -0x8000_0000 <= n and n <= 0x7fff_ffff
    return source.ExprNum(source.type_word32, n)


def i32v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word32, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def htd_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('HTD'), use_guard=True, path=()))


def mem_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('Mem'), use_guard=True, path=()))


def pms_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('PMS'), use_guard=True, path=()))


def ghost_asserts_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('GhostAssertions'), use_guard=True, path=()))


def i64v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word64, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def i64(n: int) -> source.ExprNumT:
    assert -0x8000_0000_0000_0000 <= n and n <= 0x7fff_ffff_ffff_ffff
    return source.ExprNum(source.type_word64, n)


def boolv(n: str, guard: bool) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject(n), use_guard=guard, path=()))


def g(name: str) -> source.ExprVarT[source.HumanVarName]:
    """ guard """
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=True, path=()))


i32ret = source.ExprVar(source.type_word32, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))

i64ret = source.ExprVar(source.type_word64, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))


def sbounded(var: source.ExprVarT[source.HumanVarName], lower: source.ExprT[source.HumanVarName], upper: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    return conj(sle(lower, var), sle(var, upper))

# def assigned(var: source.ExprVarT[source.HumanVarName]):
#     return source.ExprAssigned(source.type_bool, var)


def lh(x: str) -> source.LoopHeaderName:
    return source.LoopHeaderName(source.NodeName(x))


def charv(n: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word8, source.HumanVarName(source.HumanVarNameSubject(n), use_guard=False, path=()))


def char(n: int) -> source.ExprNumT:
    return source.ExprNum(source.type_word8, n)


universe = {
    "tests/all.txt": {
        # 3 <= i ==> a = 1
        # 3:w32 <=s i:w32 ==> a:w32 = 1:w32
        "tmp.undefined_var_with_loops": source.Ghost(
            loop_invariants={
                lh("5"): conj(imp(sle(i32(3), i32v("i")), eq(i32v("a"), i32(1))), sbounded(i32v("i"), i32(0), i32(5)))
            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.multiple_loops___fail_missing_invariant": source.Ghost(
            loop_invariants={
                # no need to think, i is always going to be less than 200, and
                # that's enough to prove no overflows
                lh('17'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('4'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('8'): sbounded(i32v('i'), i32(0), i32(200)),

            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.arith_sum": source.Ghost(
            loop_invariants={
                # 0 <= i <= n
                # s = i * (i - 1) / 2
                # i#assigned
                # s#assigned
                lh('5'): conjs(
                    sbounded(i32v('i'), i32(0), i32v('n')),
                    eq(i32v('s'), udiv(mul(i32v('i'), sub(i32v('i'), i32(1))), i32(2))),
                    g('i'),
                    g('s')),
            },
            precondition=sbounded(i32v('n'), i32(0), i32(100)),
            postcondition=eq(i32ret, udiv(
                mul(i32v('n'), sub(i32v('i'), i32(1))), i32(2))),
        ),

        "tmp.multiple_ret_incarnations___fail_missing_invariants": source.Ghost(
            loop_invariants={lh('5'): T},
            precondition=sle(i32(0), i32v('n')),
            postcondition=eq(i32ret, udiv(i32v('n'), i32(2))),
        )
    },
    "./examples/libsel4cp_trunc.txt": {
        "libsel4cp.handler_loop": source.Ghost(
            loop_invariants={lh('3'):
                             conjs(
                                       eq(neq(charv('have_reply'), char(0)), neq(g('reply_tag'), source.expr_false)),
                                       source.expr_implies(
                                            eq(g('is_endpoint'), T),
                                            eq(neq(i64v('is_endpoint'), i64(0)), neq(charv('have_reply'), char(0)))
                                       ),
                                       eq(g('is_endpoint'), g('reply_tag')),
                                       eq(htd_assigned(), T),
                                       eq(mem_assigned(), T),
                                       eq(pms_assigned(), T),
                                       eq(ghost_asserts_assigned(), T),
                                       eq(g('have_reply'), T), 
                                   ),
                             lh('10'): conjs(
                eq(i64v('is_endpoint'), i64(0)),
                eq(g('badge'), T),
                eq(g('idx'), T),
                eq(htd_assigned(), T),
                eq(mem_assigned(), T),
                eq(pms_assigned(), T),
                eq(ghost_asserts_assigned(), T)
            )
            },
            precondition=T,
            postcondition=T
        )
    }
}
