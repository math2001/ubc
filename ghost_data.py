from typing import Mapping, Callable, Any
import source
import nip

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
neq = source.expr_neq
neg = source.expr_negate

T = source.expr_true
F = source.expr_false

ite = source.expr_ite


def get(file_name: str, func_name: str) -> source.Ghost[source.ProgVarName | nip.GuardVarName] | None:
    if file_name.endswith('.c'):
        file_name = file_name[:-len('.c')] + '.txt'
    if file_name in universe and func_name in universe[file_name]:
        return universe[file_name][func_name]
    return None


def conjs(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    # pyright is stupid, but mypy works it out (we only care about mypy)
    if len(xs) == 0:
        return T

    return source.ExprOp(source.type_bool, source.Operator.AND, xs)
    # return reduce(source.expr_and, xs)  # pyright: ignore


def ors(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    if len(xs) == 0:
        return T
    return source.ExprOp(source.type_bool, source.Operator.OR, xs)


def i32(n: int) -> source.ExprNumT:
    assert -0x8000_0000 <= n and n <= 0x7fff_ffff
    return source.ExprNum(source.type_word32, n)


def i32v(name: str) -> source.ExprVarT[source.ProgVarName]:
    # return source.ExprVar(source.type_word32, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))
    return source.ExprVar(source.type_word32, source.ProgVarName(name + "___int#v"))


def i64v(name: str) -> source.ExprVarT[source.ProgVarName]:
    # return source.ExprVar(source.type_word64, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))
    return source.ExprVar(source.type_word64, source.ProgVarName(name + "___long#v"))


def u64v(name: str) -> source.ExprVarT[source.ProgVarName]:
    # return source.ExprVar(source.type_word64, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))
    return source.ExprVar(source.type_word64, source.ProgVarName(name + "___unsigned_long#v"))


def i64(n: int) -> source.ExprNumT:
    assert -0x8000_0000_0000_0000 <= n and n <= 0x7fff_ffff_ffff_ffff
    return source.ExprNum(source.type_word64, n)


def u64(n: int) -> source.ExprNumT:
    assert -0x8000_0000_0000_0000 <= n and n <= 0x7fff_ffff_ffff_ffff
    return source.ExprNum(source.type_word64, n)


def g(var: source.ExprVarT[source.ProgVarName] | str) -> source.ExprVarT[nip.GuardVarName]:
    """ guard """
    if isinstance(var, str):
        return source.ExprVar(source.type_bool, nip.guard_name(source.ProgVarName(var)))
    return source.ExprVar(source.type_bool, nip.guard_name(source.ProgVarName(var.name)))


def charv(n: str) -> source.ExprVarT[source.ProgVarName]:
    return source.ExprVar(source.type_word8, source.ProgVarName(n))


def char(n: int) -> source.ExprNumT:
    return source.ExprNum(source.type_word8, n)

# i32ret = source.ExprVar(source.type_word32, source.HumanVarName(
#     source.HumanVarNameSpecial.RET, use_guard=False, path=()))

# i64ret = source.ExprVar(source.type_word64, source.HumanVarName(
#     source.HumanVarNameSpecial.RET, use_guard=False, path=()))


i32ret = source.ExprVar(source.type_word32, source.CRetSpecialVar("c_ret.0"))
i32ret.name.field_num = 0


def sbounded(var: source.ExprVarT[source.ProgVarName], lower: source.ExprT[source.ProgVarName], upper: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
    return conj(sle(lower, var), sle(var, upper))

# def assigned(var: source.ExprVarT[source.HumanVarName]):
#     return source.ExprAssigned(source.type_bool, var)


def lh(x: str) -> source.LoopHeaderName:
    return source.LoopHeaderName(source.NodeName(x))


# lc = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
#     source.HumanVarNameSubject('GhostAssertions'), path=(), use_guard=False))

# lc = source.ProgVarName('GhostAssertions')

testghost = source.ExprVar(source.TypeBitVec(
    32), source.ProgVarName("test#ghost"))


# Ch = source.TypeBitVec(6)
# Set_Ch = source.TypeBitVec(64)
# Ch_set_has = source.FunctionName('Ch_set_has')
# MsgInfo = source.TypeBitVec(80)
# Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(80)
Prod_Ch_MsgInfo = source.TypeBitVec(86)

# lc_running_pd = source.FunctionName('lc_running_pd')
# lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
# lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
# lc_receive_oracle = source.FunctionName('lc_receive_oracle')

# C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
# Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Prod_Ch_MsgInfo_Just')
# C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
# C_msg_info_valid = source.FunctionName('C_msg_info_valid')

# C_channel_valid = source.FunctionName('C_channel_valid')

Ch = source.TypeBitVec(6)
PD = source.TypeBitVec(6)
NextRecv = source.TypeBitVec(72)
NextRecvEnum = source.TypeBitVec(2)
Set_Ch = source.TypeBitVec(64)
MsgInfo = source.TypeBitVec(64)
Prod_Ch_MsgInfo = source.TypeBitVec(70)
Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(71)
Maybe_MsgInfo = source.TypeBitVec(65)
Maybe_MsgInfoEnum = source.TypeBitVec(1)
SeL4_Ntfn = source.TypeBitVec(64)
Prod_MsgInfo_SeL4_Ntfn = source.TypeBitVec(128)

Ch_set_empty = source.FunctionName('Ch_set_empty')
Ch_set_has = source.FunctionName('Ch_set_has')
Ch_set_add = source.FunctionName("Ch_set_add")
Ch_set_remove = source.FunctionName("Ch_set_remove")

NextRecvEnumGet = source.FunctionName('NextRecv.<>')
NextRecvEnumNotification = source.FunctionName('<NR_Notification>')
NextRecvEnumPPCall = source.FunctionName('<NR_PPCall>')
NextRecvEnumUnknown = source.FunctionName('<NR_Unknown>')

Maybe_MsgInfoEnumGet = source.FunctionName('Maybe_MsgInfo.<>')
Maybe_MsgInfoEnumJust = source.FunctionName('<MsgInfo_Just>')
Maybe_MsgInfoEnumNothing = source.FunctionName('<MsgInfo_Nothing>')

NextRecv_Notification: source.ExprT[source.ProgVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumNotification, [])
NextRecv_PPCall: source.ExprT[source.ProgVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumPPCall, [])
NextRecv_Unknown: source.ExprT[source.ProgVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumUnknown, [])

NextRecvNotificationGet = source.FunctionName('NR_Notification.1')
NextRecvPPCallGet = source.FunctionName('NR_PPCall.1')

lc_running_pd = source.FunctionName('lc_running_pd')
lc_receive_oracle = source.FunctionName('lc_receive_oracle')
lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
lc_last_handled_notified = source.FunctionName('lc_last_handled_notified')
lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
lc_unhandled_reply = source.FunctionName('lc_unhandled_reply')
lc_last_handled_reply = source.FunctionName('lc_last_handled_reply')

Prod_Ch_MsgInfo_Nothing = source.FunctionName('Prod_Ch_MsgInfo_Nothing')
Prod_Ch_MsgInfo_fn = source.FunctionName('Prod_Ch_MsgInfo')
MsgInfo_Nothing = source.FunctionName('MsgInfo_Nothing')


C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Prod_Ch_MsgInfo_Just')
MsgInfo_Just = source.FunctionName('MsgInfo_Just')
MsgInfo_Just_1 = source.FunctionName('MsgInfo_Just.1')

MI = source.FunctionName('MI')

Prod_Ch_MsgInfo_fst = source.FunctionName('Prod_Ch_MsgInfo.fst')
Prod_Ch_MsgInfo_snd = source.FunctionName('Prod_Ch_MsgInfo.snd')

C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
C_msg_info_valid = source.FunctionName('C_msg_info_valid')
C_channel_valid = source.FunctionName('C_channel_valid')

# constructor for platform context
PlatformContext_LC = source.FunctionName('LC')
PlatformContext = source.TypeBitVec(407)

NR_Notification = source.FunctionName('NR_Notification')
NR_Unknown = source.FunctionName('NR_Unknown')

Ch_empty_fn: source.ExprT[source.ProgVarName] = source.ExprFunction(
    Set_Ch, Ch_set_empty, ())

lc_err = source.ExprNum(source.TypeBitVec(407), 0xdead1c)


def htd_assigned() -> source.ExprVarT[nip.GuardVarName]:
    return g(source.ExprVar(source.type_bool, source.ProgVarName('HTD')))


def mem_assigned() -> source.ExprVarT[nip.GuardVarName]:
    return g(source.ExprVar(source.type_bool, source.ProgVarName('Mem')))


def pms_assigned() -> source.ExprVarT[nip.GuardVarName]:
    return g(source.ExprVar(source.type_bool, source.ProgVarName('PMS')))


def ghost_asserts_assigned() -> source.ExprVarT[nip.GuardVarName]:
    return g(source.ExprVar(source.type_bool, source.ProgVarName('GhostAssertions')))


def arg(v: source.ExprVarT[source.ProgVarName]) -> source.ExprVarT[source.ProgVarName]:
    return source.ExprVar(v.typ, source.ProgVarName(v.name + "/arg"))


def handler_loop_node_name() -> str:
    return '3'


lc_progvar = source.ExprVar(source.TypeBitVec(
    407), source.ProgVarName('local_context'))

handle_loop_pre_oracle: source.ExprT[Any] = source.ExprFunction(
    NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])
handle_loop_pre_oracle_ty: source.ExprT[Any] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumGet, [handle_loop_pre_oracle])
handle_loop_pre_unhandled_reply: source.ExprT[Any] = source.ExprFunction(
    Maybe_MsgInfo, source.FunctionName('handler_loop_pre_unhandled_reply'), [])

recv_oracle_kernel: source.ExprT[Any] = source.ExprFunction(
    Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])


def platform_context_update(
    base_lc: source.ExprT[source.ProgVarName],
    *,
    lc_running_pd_val: source.ExprT[source.ProgVarName] | None = None,
    lc_receive_oracle_val: source.ExprT[source.ProgVarName] | None = None,
    lc_unhandled_notified_val: source.ExprT[source.ProgVarName] | None = None,
    lc_last_handled_notified_val: source.ExprT[source.ProgVarName] | None = None,
    lc_unhandled_ppcall_val: source.ExprT[source.ProgVarName] | None = None,
    lc_unhandled_reply_val: source.ExprT[source.ProgVarName] | None = None,
    lc_last_handled_reply_val: source.ExprT[source.ProgVarName] | None = None,
) -> source.ExprT[source.ProgVarName]:
    """
    Copies every field from base_lc, apart from the specified fields.

    This matches the update syntax in haskell. When we write

        lc' = lc { f1: v1, f2: v2, ... },

    we use

        lc' platform_context_update(lc, f1=v1, f2=v2, ...).

    """
    fields = [lc_running_pd, lc_receive_oracle, lc_unhandled_notified,
              lc_last_handled_notified, lc_unhandled_ppcall, lc_unhandled_reply, lc_last_handled_reply]
    vals = [lc_running_pd_val, lc_receive_oracle_val, lc_unhandled_notified_val, lc_last_handled_notified_val,
            lc_unhandled_ppcall_val, lc_unhandled_reply_val, lc_last_handled_reply_val]
    typs = [PD, NextRecv, Set_Ch, Set_Ch,
            Maybe_Prod_Ch_MsgInfo, Maybe_MsgInfo, Maybe_MsgInfo]

    arguments: list[source.ExprT[source.ProgVarName]] = []

    for i, (field, val, typ) in enumerate(zip(fields, vals, typs)):
        new_value: source.ExprT[source.ProgVarName]
        if val is None:
            new_value = source.ExprFunction(typ, field, [base_lc])
        else:
            assert val.typ == typ, f"argument {i+1} (1-based), namely {field}, should have typ {typ}, got {val.typ}"
            new_value = val

        arguments.append(new_value)

    # needs the arguments to be in the same order
    return source.ExprFunction(PlatformContext, PlatformContext_LC, arguments)


def mi_zeroed() -> source.ExprT[source.ProgVarName]:
    return source.ExprFunction(MsgInfo, MI, [source.ExprNum(source.type_word52, 0), source.ExprNum(source.type_word12, 0)])


mi_err: source.ExprT[source.ProgVarName]
mi_err = source.ExprFunction(MsgInfo, MI, [source.ExprNum(
    source.type_word52, 0xd), source.ExprNum(source.type_word12, 0xd)])


def NextRecv_case(
        nr: source.ExprT[source.ProgVarName],
        NR_Notification: Callable[[source.ExprT[source.ProgVarName]], source.ExprT[source.ProgVarName]],
        NR_PPCall: Callable[[source.ExprT[source.ProgVarName]], source.ExprT[source.ProgVarName]],
        NR_Unknown: Callable[[], source.ExprT[source.ProgVarName]]) -> source.ExprT[source.ProgVarName]:
    """
    Relies on the assumption that every constructor is distinct. This is
    established in gen.py
    """

    set_ch = source.ExprFunction(Set_Ch, NextRecvNotificationGet, [nr])

    # next_recv_ppcall = source.ExprFunction(Prod_Ch_MsgInfo,
    prod_ch_msginfo = source.ExprFunction(
        Prod_Ch_MsgInfo, NextRecvPPCallGet, [nr])

    constructor = source.ExprFunction(NextRecvEnum, NextRecvEnumGet, [nr])

    is_notif = eq(constructor, NextRecv_Notification)
    is_ppcall = eq(constructor, NextRecv_PPCall)
    # this one is deduced (all the constructors are distinct)
    is_unknown = eq(constructor, NextRecv_Unknown)

    return ite(is_notif, NR_Notification(set_ch), ite(is_ppcall, NR_PPCall(prod_ch_msginfo), NR_Unknown()))


def recv_postcondition(rv: source.ExprT[source.ProgVarName], arg_lc: source.ExprVarT[source.ProgVarName], ret_lc: source.ExprVarT[source.ProgVarName], ret_var: source.ExprVarT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:

    def rv_when_notification(_: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return mi_zeroed()

    def rv_when_ppcall(prod_ch_msginfo: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return source.ExprFunction(MsgInfo, Prod_Ch_MsgInfo_snd, [prod_ch_msginfo])

    def rv_when_unknown() -> source.ExprT[source.ProgVarName]:
        return mi_err

    def lc_when_notification(notis: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_notified_val=notis,
        )

    def lc_when_ppcall(prod_ch_msginfo: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_ppcall_val=source.ExprFunction(
                Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [prod_ch_msginfo])
        )

    def lc_when_unknown() -> source.ExprT[source.ProgVarName]:
        return lc_err

    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, [arg_lc])

    rv = NextRecv_case(oracle, rv_when_notification,
                       rv_when_ppcall, rv_when_unknown)
    lc_prime = NextRecv_case(oracle, lc_when_notification,
                             lc_when_ppcall, lc_when_unknown)

    mem = source.ExprVar(source.type_mem, source.ProgVarName('Mem'))

    gbadge: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName('badge'), [])
    mem_condition: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName("mem-acc"), [mem, gbadge])

    recv_oracle_kernel: source.ExprT[source.ProgVarName] = source.ExprFunction(
        Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])
    recv_badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])

    return conjs(
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [ret_var]),
            rv
        ),
        eq(ret_lc, lc_prime),
        eq(mem_condition, recv_badge)
    )


universe: Mapping[str, Mapping[str, source.Ghost[source.ProgVarName | nip.GuardVarName]]] = {
    "tests/errors/errors.txt": {
        "tmp.private_hello": source.Ghost(
            precondition=eq(arg(i32v('hx')), i32(0)),
            postcondition=T,
            loop_invariants={}
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
                    g(i32v('i')),
                    g(i32v('s'))),
            },
            precondition=sbounded(arg(i32v('n')), i32(0), i32(100)),
            postcondition=T,
            # postcondition=eq(i32ret, udiv(
            #     mul(arg(i32v('n')), sub(arg(i32v('i')), i32(1))), i32(2))),
        ),

        "tmp.multiple_ret_incarnations___fail_missing_invariants": source.Ghost(
            loop_invariants={lh('5'): T},
            precondition=sle(i32(0), arg(i32v('n'))),
            postcondition=eq(i32ret, udiv(arg(i32v('n')), i32(2))),
        ),

        "tmp.callee": source.Ghost(
            loop_invariants={},
            precondition=sle(arg(i32v('a')), i32(100)),
            postcondition=eq(i32ret, plus(arg(i32v('a')), i32(1)))
        ),

        "tmp.caller": source.Ghost(
            loop_invariants={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, mul(plus(arg(i32v('b')), i32(1)), i32(2)))),

        "tmp.caller2": source.Ghost(
            loop_invariants={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, mul(plus(arg(i32v('b')), i32(1)), mul(plus(arg(i32v('b')), i32(1)), i32(2))))),

        "tmp.caller2___fails_wrong_post_condition": source.Ghost(
            loop_invariants={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, i32(0))),

        "tmp.caller3": source.Ghost(
            loop_invariants={},
            precondition=sbounded(arg(i32v('b')), i32(-100), i32(100)),
            postcondition=eq(i32ret, i32(0))),

        "tmp.f_many_args": source.Ghost(
            loop_invariants={},
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
            precondition=conjs(sbounded(arg(i32v('x')), i32(-10), i32(10)),
                               sbounded(arg(i32v('y')), i32(-10), i32(10))),
            postcondition=eq(i32ret, mul(sub(arg(i32v('y')), i32(1)), i32(2))),
        ),

        "tmp.ghost_add_1__fail": source.Ghost(loop_invariants={},
                                              precondition=T,
                                              postcondition=eq(testghost, plus(arg(testghost), i32(1)))),

        "tmp.ghost_add_3": source.Ghost(loop_invariants={},
                                        precondition=T,
                                        postcondition=eq(testghost, plus(arg(testghost), i32(3)))),
        "tmp.ghost_add_2__fail": source.Ghost(loop_invariants={},
                                              precondition=T,
                                              postcondition=eq(testghost, plus(arg(testghost), i32(2)))),

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
            precondition=sbounded(arg(i32v('n')), i32(0), i32(10)),
            postcondition=eq(testghost, plus(arg(testghost), plus(arg(i32v('n')), i32(1)))))
        # the +1 breaks everything here
    },
    "tests/libsel4cp_trunc.txt": {
        "libsel4cp.protected": source.Ghost(
            precondition=conjs(
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc_progvar, )),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [
                       source.ExprFunction(Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_fn, (
                           # unsigned int is i64??
                           source.ExprFunction(
                               Ch, C_channel_to_SMT_channel, (i32v('ch'), )),
                           source.ExprFunction(
                               MsgInfo, C_msg_info_to_SMT_msg_info, (i64v('msginfo'), )),
                       ))
                   ])),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i32v('ch'), )),
            ),
            postcondition=T,
            loop_invariants={}
        ),
        "libsel4cp.notified": source.Ghost(precondition=T, postcondition=T, loop_invariants={}),
        "libsel4cp.seL4_Recv": source.Ghost(precondition=T, postcondition=T, loop_invariants={}),
        "libsel4cp.seL4_ReplyRecv": source.Ghost(precondition=T, postcondition=T, loop_invariants={}),
        "libsel4cp.handler_loop": source.Ghost(loop_invariants={
            lh(handler_loop_node_name()): conjs(
                source.expr_implies(
                    neq(charv('have_reply____Bool#v'), char(0)),
                    eq(g('reply_tag___struct_seL4_MessageInfo_C#v.words_C.0'), T),
                ),
                source.expr_implies(
                    eq(g('is_endpoint___unsigned_long#v'), T),
                    eq(
                        neq(u64v('is_endpoint'), u64(0)),
                        neq(charv('have_reply____Bool#v'),
                            char(0))
                    )
                ),
                eq(htd_assigned(), T),
                eq(mem_assigned(), T),
                eq(pms_assigned(), T),
                eq(ghost_asserts_assigned(), T),
                eq(g('have_reply____Bool#v'), T),
                eq(g("test#ghost"), T)
            ),
            lh('10'): conjs(
                eq(u64v('is_endpoint'), u64(0)),
                eq(g('lbadge___unsigned_long#v'), T),
                eq(g('idx___unsigned#v'), T),
                eq(htd_assigned(), T),
                eq(mem_assigned(), T),
                eq(pms_assigned(), T),
                eq(ghost_asserts_assigned(), T),
                eq(g("test#ghost"), T)
            )
        }, precondition=T, postcondition=T)
    }
}


def wf_handler_pre_unhandled_reply_with_set_ghost() -> source.ExprT[source.ProgVarName]:
    wf_condition = conjs(
        # if Nothing then all other bits are zero
        source.expr_implies(
            eq(
                source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                                    handle_loop_pre_unhandled_reply]),
                source.ExprFunction(Maybe_MsgInfoEnum,
                                    Maybe_MsgInfoEnumNothing, [])
            ),
            conjs(
                eq(
                    handle_loop_pre_unhandled_reply,
                    source.ExprNum(Maybe_MsgInfo, 0)
                ),
                eq(
                    source.ExprFunction(source.TypeBitVec(
                        8), source.FunctionName("have_reply____Bool@v~2"), []),
                    source.ExprNum(source.type_word8, 0)
                )
            )
        ),
        # if no have_reply then no unhandled_reply either
        source.expr_implies(
            eq(
                source.ExprFunction(source.TypeBitVec(
                    8), source.FunctionName("have_reply____Bool@v~2"), []),
                source.ExprNum(source.type_word8, 0)
            ),
            eq(
                source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                                    handle_loop_pre_unhandled_reply]),
                source.ExprFunction(Maybe_MsgInfoEnum,
                                    Maybe_MsgInfoEnumNothing, [])
            )
        )
    )

    return conjs(
        wf_condition,
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [lc_progvar]),
            handle_loop_pre_unhandled_reply
        )
    )


def wf_handler_pre_receive_oracle_with_set_ghost() -> source.ExprT[source.ProgVarName]:
    # the top two bits are valid.
    # check if the receive oracle is a valid enum

    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    valid_enum = ors(
        is_notification,
        eq(
            handle_loop_pre_oracle_ty,
            source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
        ),
    )

    valid_pre_handler_notification = source.expr_implies(
        is_notification,
        conjs(
            neq(
                source.ExprFunction(Set_Ch, NextRecvNotificationGet, [
                                    handle_loop_pre_oracle]),
                source.ExprFunction(Set_Ch, Ch_set_empty, [])
            ),
        )
    )

    # we sort of don't care about sections of the bitvector we don't access
    # as a result we can just assume its correct, even though it might not be.
    valid_ppcall = T
    valid_unknown = T
    wf_receive = conjs(
        valid_enum, valid_pre_handler_notification, valid_ppcall, valid_unknown)

    return conjs(
        wf_receive,
        eq(
            source.ExprFunction(NextRecv, lc_receive_oracle, [lc_progvar]),
            handle_loop_pre_oracle
        )
    )


def receive_oracle_relation() -> source.ExprT[source.ProgVarName]:
    # case 1: notis
    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    notification = source.ExprFunction(
        Set_Ch, NextRecvNotificationGet, [handle_loop_pre_oracle])

    badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])

    ch_checks: list[source.ExprT[source.ProgVarName]] = []

    # eq check instead of badge_has_channel (which made dsa graph too wide)
    ch_checks = [
        eq(notification, badge),
        eq(
            i64(0),
            source.expr_shift_right(
                badge,
                i64(63)
            )
        ),
        eq(
            source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"), [
                source.ExprFunction(source.type_word64,
                                    lc_unhandled_notified, [lc_progvar]),
                source.ExprFunction(source.type_word64,
                                    lc_last_handled_notified, [lc_progvar])
            ]),
            source.ExprFunction(source.type_word64,
                                source.FunctionName("Ch_set_empty"), [])
        ),
    ]

    # case 2: ppcalls
    is_ppcall = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumPPCall, [])
    )

    the_ppcall = source.ExprFunction(
        Prod_Ch_MsgInfo, NextRecvPPCallGet, [handle_loop_pre_oracle])

    the_ch = source.ExprFunction(
        Ch, Prod_Ch_MsgInfo_fst, [the_ppcall])

    the_msginfo = source.ExprFunction(
        MsgInfo, Prod_Ch_MsgInfo_snd, [the_ppcall])

    # reply pending
    no_reply_pending = eq(
        source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                            handle_loop_pre_unhandled_reply]),
        source.ExprFunction(Maybe_MsgInfoEnum,
                            Maybe_MsgInfoEnumNothing, [])
    )

    have_reply_lvar: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.TypeBitVec(8), source.FunctionName("have_reply____Bool@v~2"), [])
    rt_assigned_lvar: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_bool, source.FunctionName("reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2"), [])

    no_reply_pending_kernel = conjs(
        eq(have_reply_lvar, char(0)),
        eq(rt_assigned_lvar, T)
    )

    relation = conjs(
        source.expr_implies(
            is_notification,
            conjs(*ch_checks)
        ),
        source.expr_implies(
            no_reply_pending,
            no_reply_pending_kernel
        ),
        source.expr_implies(
            no_reply_pending_kernel,
            no_reply_pending
        )
    )

    return relation


def handler_loop_iter_pre() -> source.ExprT[source.ProgVarName]:

    return conjs(
        # lc_unhandled_reply lc = lc_unhandled_reply_pre
        wf_handler_pre_unhandled_reply_with_set_ghost(),

        eq(
            source.ExprFunction(Set_Ch, lc_unhandled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),
        # this cond is required, but was missing from the dec 5 version of the spec:
        eq(
            source.ExprFunction(
                Set_Ch, lc_last_handled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),

        # so is this cond: no unhandled replies at start!
        eq(
            source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar])]),
            source.ExprFunction(Maybe_MsgInfoEnum,
                                Maybe_MsgInfoEnumNothing, [])
        ),
        eq(
            source.ExprFunction(MsgInfo, MsgInfo_Just_1, [
                source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar])]),
            i64(0)
        ),
        eq(
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                lc_unhandled_ppcall, [lc_progvar]),
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                Prod_Ch_MsgInfo_Nothing, [])
        ),

        # lc_receive_oracle lc = lc_receive_oracle_pre
        wf_handler_pre_receive_oracle_with_set_ghost(),
        receive_oracle_relation(),
    )


def handler_loop_iter_post() -> source.ExprT[source.ProgVarName]:

    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    return conjs(
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar]),
            handle_loop_pre_unhandled_reply
        ),
        eq(
            source.ExprFunction(Set_Ch, lc_unhandled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),
        eq(
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                lc_unhandled_ppcall, [lc_progvar]),
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                Prod_Ch_MsgInfo_Nothing, [])
        ),
        eq(
            source.ExprFunction(NextRecv, lc_receive_oracle, [lc_progvar]),
            source.ExprFunction(NextRecv, NR_Unknown, [])
        ),
        source.expr_implies(
            is_notification,
            eq(
                source.ExprFunction(
                    Set_Ch, lc_last_handled_notified, [lc_progvar]),
                source.ExprFunction(Set_Ch, NextRecvNotificationGet, [
                                    handle_loop_pre_oracle])
            )
        )
    )
