from typing import Mapping, Any
import source
import nip
import sel4cp_spec
from ghost_data_helpers import *


def get(file_name: str, func_name: str) -> source.Ghost[source.ProgVarName | nip.GuardVarName] | None:
    if file_name.endswith('.c'):
        file_name = file_name[:-len('.c')] + '.txt'
    if file_name in universe and func_name in universe[file_name]:
        return universe[file_name][func_name]
    return None


testghost = source.ExprVar(source.TypeBitVec(
    32), source.ProgVarName("test#ghost"))


universe: Mapping[str, Mapping[str, source.Ghost[source.ProgVarName | nip.GuardVarName]]] = {
    "tests/errors/errors.txt": {
        "tmp.private_hello": source.Ghost(
            precondition=eq(arg(i32v('hx')), i32(0)),
            postcondition=T,
            loop_invariants={},
            loop_iterations={},
        )
    },
    "tests/all.txt": {
        # 3 <= i ==> a = 1
        # 3:w32 <=s i:w32 ==> a:w32 = 1:w32
        "tmp.undefined_var_with_loops": source.Ghost(
            loop_invariants={
                lh("5"): conj(imp(sle(i32(3), i32v("i")), eq(i32v("a"), i32(1))), sbounded(i32v("i"), i32(0), i32(5)))
            },
            precondition=T,
            postcondition=T,
            loop_iterations={
                lh('5'): source.empty_loop_ghost,
            },
        ),

        "tmp.multiple_loops___fail_missing_invariant": source.Ghost(
            loop_invariants={
                # no need to think, i is always going to be less than 200, and
                # that's enough to prove no overflows
                lh('17'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('4'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('8'): sbounded(i32v('i'), i32(0), i32(200)),
            },
            loop_iterations={
                lh('17'): source.empty_loop_ghost,
                lh('4'): source.empty_loop_ghost,
                lh('8'): source.empty_loop_ghost,
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
                    g(i32v('i')),
                    g(i32v('s'))),
            },
            precondition=sbounded(arg(i32v('n')), i32(0), i32(100)),
            postcondition=T,
            # postcondition=eq(i32ret, udiv(
            #     mul(arg(i32v('n')), sub(arg(i32v('i')), i32(1))), i32(2))),
            loop_iterations={lh('5'): source.empty_loop_ghost},
        ),

        "tmp.multiple_ret_incarnations___fail_missing_invariants": source.Ghost(
            loop_invariants={lh('5'): T},
            loop_iterations={lh('5'): source.empty_loop_ghost},
            precondition=sle(i32(0), arg(i32v('n'))),
            postcondition=eq(i32ret, udiv(arg(i32v('n')), i32(2))),
        ),

        "tmp.callee": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sle(arg(i32v('a')), i32(100)),
            postcondition=eq(i32ret, plus(arg(i32v('a')), i32(1)))
        ),

        "tmp.caller": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, mul(plus(arg(i32v('b')), i32(1)), i32(2)))),

        "tmp.caller2": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, mul(plus(arg(i32v('b')), i32(1)), mul(plus(arg(i32v('b')), i32(1)), i32(2))))),

        "tmp.caller2___fails_wrong_post_condition": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, i32(0))),

        "tmp.caller3": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, i32(0))),

        "tmp.f_many_args": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=conjs(
                sbounded(arg(i32v('b')), i32(-100), i32(100)),
                sbounded(arg(i32v('c')), i32(-100), i32(100))
            ),
            postcondition=conjs(
                imp(slt(i32(0), arg(i32v('a'))), eq(
                    i32ret, mul(plus(arg(i32v('b')), i32(1)), i32(2)))),
                imp(neg(slt(i32(0), arg(i32v('a')))), eq(
                    i32ret, mul(sub(arg(i32v('c')), i32(1)), i32(2)))),
            ),
        ),

        "tmp.call_many_args": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=sbounded(arg(i32v('flag')), i32(-10), i32(10)),
            postcondition=conjs(
                # imp(slt(i32(0), arg(i32v('flag'))), eq(i32ret, plus(
                #     i32(4), mul(plus(arg(i32v('flag')), i32(1)), i32(2))))),
                # imp(neg(slt(i32(0), arg(i32v('flag')))), eq(i32ret, plus(
                #     i32(2), mul(sub(arg(i32v('flag')), i32(1)), i32(2))))),
                T,
                imp(eq(arg(i32v('flag')), i32(0)),
                    eq(i32ret, i32(0))),

            ),
        ),

        "tmp.call_many_args_once": source.Ghost(
            loop_invariants={},
            loop_iterations={},
            precondition=conjs(sbounded(arg(i32v('x')), i32(-10), i32(10)),
                               sbounded(arg(i32v('y')), i32(-10), i32(10))),
            postcondition=eq(i32ret, mul(sub(arg(i32v('y')), i32(1)), i32(2))),
        ),

        "tmp.ghost_add_1__fail": source.Ghost(loop_invariants={},
                                              loop_iterations={},
                                              precondition=T,
                                              postcondition=eq(testghost, plus(arg(testghost), i32(1)))),

        "tmp.ghost_add_3": source.Ghost(loop_invariants={},
                                        loop_iterations={},
                                        precondition=T,
                                        postcondition=eq(testghost, plus(arg(testghost), i32(3)))),
        "tmp.ghost_add_2__fail": source.Ghost(loop_invariants={},
                                              loop_iterations={},
                                              precondition=T,
                                              postcondition=eq(testghost, plus(arg(testghost), i32(2)))),

        "tmp.special_call__fail": source.Ghost(loop_invariants={},
                                               loop_iterations={},
                                               precondition=slt(
                                                   plus(arg(testghost), arg(i32v('i'))), i32(255)),
                                               postcondition=eq(testghost, i32(0))),

        "tmp.loop_iteration_condition": source.Ghost(
            loop_invariants={
                lh('3'): conjs(g(testghost),
                               g(i32v('i')),
                               g('Mem'),
                               g('PMS'),
                               g('HTD'),
                               g('GhostAssertions'),
                               sbounded(i32v('i'), i32(0), i32(10))),
            },
            loop_iterations={
                lh('3'): source.LoopIterationGhost(
                    pre_iter=sbounded(testghost, i32(0), i32(127)),
                    post_iter=eq(testghost, i32(0)),
                )
            },
            precondition=T,
            postcondition=T),

        "tmp.concrete_ghost_interaction": source.Ghost(
            loop_invariants={
                lh('3'): conjs(g(i32v('i')),
                               g(i32v('n')),
                               g('GhostAssertions'),
                               g('Mem'),
                               g(testghost),
                               g('PMS'),
                               g('HTD'),
                               sbounded(i32v('i'), i32(0), i32v('n')),
                               eq(testghost, plus(arg(testghost), i32v('i')))
                               )
            },
            loop_iterations={lh('3'): source.empty_loop_ghost},
            precondition=sbounded(arg(i32v('n')), i32(0), i32(10)),
            postcondition=eq(testghost, plus(arg(testghost), arg(i32v('n'))))),

        "tmp.concrete_ghost_interaction__fail": source.Ghost(
            loop_invariants={
                lh('3'): conjs(g(i32v('i')),
                               g(i32v('n')),
                               g('GhostAssertions'),
                               g('Mem'),
                               g(testghost),
                               g('PMS'),
                               g('HTD'),
                               sbounded(i32v('i'), i32(0), i32v('n')),
                               eq(testghost, plus(arg(testghost), i32v('i')))
                               )
            },
            loop_iterations={lh('3'): source.empty_loop_ghost},
            precondition=sbounded(arg(i32v('n')), i32(0), i32(10)),
            postcondition=eq(testghost, plus(arg(testghost), plus(arg(i32v('n')), i32(1)))))
        # the +1 breaks everything here
    },
    "tests/libsel4cp_trunc.txt": sel4cp_spec.functions_spec
}
