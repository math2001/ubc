"""
This is a translation of the specification written in haskell. If you just
want to read the spec, it is much easier to read that instead.

TODO: where can you find it
"""

from typing import Callable, Any
import source
import nip
from ghost_data_helpers import *

msginfo = source.ExprVar(source.type_word64, source.ProgVarName(
    'msginfo___struct_seL4_MessageInfo_C#v.words_C.0'))

msg_info_ret = source.ExprVar(source.type_word64, source.CRetSpecialVar(
    'rv#space#ret__struct_seL4_MessageInfo_C#v.words_C.0'))
msg_info_ret.name.field_num = 0

Prod_Ch_MsgInfo = source.TypeBitVec(86)

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


def handler_loop_node_name() -> str:
    return '3'


lc_progvar = source.ExprVar(typ=source.TypeBitVec(
    407), name=source.ProgVarName("local_context#ghost"))


def lc_assigned() -> source.ExprVarT[nip.GuardVarName]:
    return g(lc_progvar)


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


def recv_postcondition(arg_lc: source.ExprVarT[source.ProgVarName], ret_lc: source.ExprVarT[source.ProgVarName], ret_var: source.ExprVarT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:

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
        source.type_word64, source.FunctionName('badge@global-symbol'), [])
    mem_condition: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName("load-word64"), [mem, gbadge])

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


def replyrecv_postcondition(arg_lc: source.ExprVarT[source.ProgVarName], ret_lc: source.ExprVarT[source.ProgVarName], ret_var: source.ExprVarT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:

    # NR_Notification notis -> lc
    #   { lc_receive_oracle = NR_Unknown
    #   , lc_unhandled_notified = notis
    #   , lc_unhandled_reply = Nothing
    #   , lc_last_handled_reply = lc_unhandled_reply lc
    #   }
    def lc_when_notification(notis: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_notified_val=notis,
            lc_unhandled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, MsgInfo_Nothing, ()),
            lc_last_handled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [arg_lc]),
        )

    # NR_PPCall ppc -> lc
    #   { lc_receive_oracle = NR_Unknown
    #   , lc_unhandled_ppcall = Just ppc
    #   , lc_unhandled_reply = Nothing
    #   , lc_last_handled_reply = lc_unhandled_reply lc
    #   }
    def lc_when_ppcall(ppc: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_ppcall_val=source.ExprFunction(
                Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [ppc]),
            lc_unhandled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, MsgInfo_Nothing, []),
            lc_last_handled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [arg_lc]),
        )

    # _ ->  error "sel4cp_correspondence_replyrecv_wp: Precondition violation."
    def lc_when_unknown() -> source.ExprT[source.ProgVarName]:
        return lc_err

    # lc' = case lc_receive_oracle lc of ...
    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, [arg_lc])
    lc_prime = NextRecv_case(oracle, lc_when_notification,
                             lc_when_ppcall, lc_when_unknown)

    # lc case DONE

    recv_oracle_kernel: source.ExprT[source.ProgVarName] = source.ExprFunction(
        Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])
    recv_badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])
    mem = source.ExprVar(source.type_mem, source.ProgVarName('Mem'))
    gbadge: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName('badge@global-symbol'), [])
    mem_condition: source.ExprT[source.ProgVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName("load-word64"), [mem, gbadge])

    # NR_Notification notis -> MI 0 0
    def rv_when_notification(_: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return mi_zeroed()

    # NR_PPCall (_, mi) -> mi
    def rv_when_ppcall(prod_ch_msginfo: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
        return source.ExprFunction(MsgInfo, Prod_Ch_MsgInfo_snd, [prod_ch_msginfo])

    # _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation in rv."
    def rv_when_unknown() -> source.ExprT[source.ProgVarName]:
        return mi_err

    # def mem_when_notification()

    rv = NextRecv_case(oracle, rv_when_notification,
                       rv_when_ppcall, rv_when_unknown)
    # rv case DONE

    return conjs(
        eq(ret_lc, lc_prime),
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [ret_var]),
            rv
        ),
        eq(mem_condition, recv_badge)
    )


def protected_postcondition(arg_lc: source.ExprT[source.ProgVarName], ret_lc: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
    lc_prime = platform_context_update(arg_lc, lc_unhandled_ppcall_val=source.ExprFunction(
        Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, ()))
    return eq(ret_lc, lc_prime)


def notified_postcondition(arg_lc: source.ExprT[source.ProgVarName], ret_lc: source.ExprT[source.ProgVarName]) -> source.ExprT[source.ProgVarName]:
    lc_prime = platform_context_update(
        arg_lc,
        lc_unhandled_notified_val=source.ExprFunction(Set_Ch, Ch_set_remove,
                                                      (source.ExprFunction(Set_Ch,  lc_unhandled_notified, (arg_lc, ), ),
                                                       source.ExprFunction(
                                                          Ch, C_channel_to_SMT_channel, (arg(u32v('ch')),))
                                                       )),
        lc_last_handled_notified_val=source.ExprFunction(Set_Ch, Ch_set_add, [
            source.ExprFunction(
                Set_Ch, lc_last_handled_notified, (arg_lc,)),
            source.ExprFunction(
                Ch, C_channel_to_SMT_channel, (arg(u32v('ch')),))])
    )

    return eq(ret_lc, lc_prime)


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
                    have_reply,
                    source.ExprNum(source.type_word8, 0)
                )
            )
        ),
        # if no have_reply then no unhandled_reply either
        source.expr_implies(
            eq(
                have_reply,
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

    have_reply_lvar = C_boolv("have_reply")
    rt_assigned_lvar = g(reply_tag)

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


idx = u32v('idx')
ch = u32v('ch')
have_reply = C_boolv('have_reply')
is_endpoint = u64v('is_endpoint')
reply_tag = source.ExprVar(source.type_word64, source.ProgVarName(
    'reply_tag___struct_seL4_MessageInfo_C#v.words_C.0'))
lbadge = u64v('lbadge')


functions_spec = {
    "libsel4cp.protected": source.Ghost(
        precondition=conjs(
            eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (arg(lc_progvar), )),
               source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [
                   source.ExprFunction(Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_fn, (
                       source.ExprFunction(
                           Ch, C_channel_to_SMT_channel, (arg(ch), )),
                       source.ExprFunction(
                           MsgInfo, C_msg_info_to_SMT_msg_info, (arg(msginfo), )),
                   ))
               ])),
            source.ExprFunction(
                source.type_bool, C_channel_valid, (arg(ch), )),
        ),
        postcondition=protected_postcondition(arg(lc_progvar), lc_progvar),
        loop_invariants={},
        loop_iterations={},
    ),
    "libsel4cp.notified": source.Ghost(
        precondition=conjs(
            source.ExprFunction(source.type_bool, Ch_set_has, (
                source.ExprFunction(
                    Set_Ch, lc_unhandled_notified, (arg(lc_progvar), )),
                source.ExprFunction(
                    Ch, C_channel_to_SMT_channel, (arg(ch), )),
            )),
            source.ExprFunction(
                source.type_bool, C_channel_valid, (arg(ch), )),
        ),
        postcondition=notified_postcondition(arg(lc_progvar), lc_progvar),
        loop_invariants={},
        loop_iterations={},
    ),
    "libsel4cp.seL4_Recv": source.Ghost(
        precondition=conjs(
            neq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg(lc_progvar),)),
                source.ExprFunction(NextRecv, NR_Unknown, ())),
            neq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg(lc_progvar),)),
                source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,))),
            eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (arg(lc_progvar),)),
               Ch_empty_fn),
            eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (arg(lc_progvar),)),
               source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
            eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (arg(lc_progvar),)),
               source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])),
        ),
        postcondition=recv_postcondition(
            arg(lc_progvar), lc_progvar, msg_info_ret),
        loop_invariants={},
        loop_iterations={},
    ),
    "libsel4cp.seL4_ReplyRecv": source.Ghost(
        precondition=conjs(
            neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg(lc_progvar),)),
                   source.ExprFunction(NextRecv, NR_Unknown, []))),
            neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg(lc_progvar),)),
                   source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,)))),
            eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (arg(lc_progvar),)),
               Ch_empty_fn),
            eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (arg(lc_progvar),)),
               source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
            neg(eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (arg(lc_progvar),)),
                   source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, []))),
        ),
        postcondition=replyrecv_postcondition(
            arg(lc_progvar), lc_progvar, msg_info_ret),
        loop_invariants={},
        loop_iterations={},
    ),
    "libsel4cp.handler_loop": source.Ghost(
        loop_invariants={
            lh(handler_loop_node_name()): conjs(
                source.expr_implies(
                    neq(have_reply, char(0)),
                    eq(g(reply_tag), T),
                ),
                source.expr_implies(
                    eq(g(is_endpoint), T),
                    eq(
                        neq(is_endpoint, u64(0)),
                        neq(have_reply,
                            char(0))
                    )
                ),
                eq(htd_assigned(), T),
                eq(mem_assigned(), T),
                eq(pms_assigned(), T),
                eq(lc_assigned(), T),
                eq(ghost_asserts_assigned(), T),
                eq(g(have_reply), T),
                eq(g(lc_progvar), T),

                source.expr_implies(
                    conjs(eq(g(lbadge), T), eq(lbadge, i64(0))),
                    conjs(
                        eq(is_endpoint, i64(0)),
                        eq(g(lbadge), T),
                        eq(g(idx), T),
                        eq(htd_assigned(), T),
                        eq(mem_assigned(), T),
                        eq(pms_assigned(), T),
                        eq(lc_assigned(), T),
                        eq(ghost_asserts_assigned(), T),
                        # required for verification (loop 10 exit conds):
                        eq(
                            lbadge,
                            source.expr_shift_right(
                                source.ExprFunction(
                                    source.type_word64, lc_unhandled_notified, [lc_progvar]),
                                source.ExprFunction(source.type_word64, source.FunctionName(
                                    "(_ zero_extend 32)"), [idx])
                            )
                        ),
                        eq(
                            source.expr_shift_left(
                                lbadge,
                                source.ExprFunction(source.type_word64, source.FunctionName(
                                    "(_ zero_extend 32)"), [idx])
                            ),
                            source.ExprFunction(
                                source.type_word64, lc_unhandled_notified, [lc_progvar]),
                        ),
                        ule(
                            idx,
                            u32(63)
                        ),
                        eq(
                            i64(0),
                            source.expr_shift_right(
                                source.ExprFunction(
                                    source.type_word64, lc_unhandled_notified, [lc_progvar]),
                                i64(63)
                            )
                        ),
                        eq(
                            i64(0),
                            source.expr_shift_right(
                                lbadge,
                                i64(63)
                            )
                        ),
                        eq(
                            source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"), [
                                source.ExprFunction(
                                    source.type_word64, lc_unhandled_notified, [lc_progvar]),
                                source.ExprFunction(
                                    source.type_word64, lc_last_handled_notified, [lc_progvar])
                            ]),
                            source.ExprFunction(
                                source.type_word64, source.FunctionName("Ch_set_empty"), [])
                        ),
                        eq(
                            source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_union"), [
                                source.ExprFunction(
                                    source.type_word64, lc_unhandled_notified, [lc_progvar]),
                                source.ExprFunction(
                                    source.type_word64, lc_last_handled_notified, [lc_progvar])
                            ]),
                            source.ExprFunction(Set_Ch, NextRecvNotificationGet, [source.ExprFunction(
                                NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])])
                        ),
                        eq(
                            source.ExprFunction(
                                Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, []),
                            source.ExprFunction(
                                Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, [lc_progvar]),
                        ),
                        eq(
                            source.ExprFunction(Maybe_MsgInfo, source.FunctionName(
                                "handler_loop_pre_unhandled_reply"), []),
                            source.ExprFunction(
                                Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar]),
                        ),
                        eq(
                            source.ExprFunction(NextRecv, NR_Unknown, []),
                            source.ExprFunction(
                                NextRecv, lc_receive_oracle, [lc_progvar]),
                        ),
                    )
                ),
            ),
            lh('10'): conjs(
                eq(is_endpoint, u64(0)),
                eq(g(lbadge), T),
                eq(g(idx), T),
                eq(htd_assigned(), T),
                eq(mem_assigned(), T),
                eq(pms_assigned(), T),
                eq(lc_assigned(), T),
                eq(ghost_asserts_assigned(), T),
                eq(g(lc_progvar), T),

                # required for functional correctness
                eq(
                    lbadge,
                    source.expr_shift_right(
                        source.ExprFunction(
                            source.type_word64, lc_unhandled_notified, [lc_progvar]),
                        source.ExprFunction(source.type_word64, source.FunctionName(
                            "(_ zero_extend 32)"), [idx])
                    )
                ),
                eq(
                    source.expr_shift_left(
                        lbadge,
                        source.ExprFunction(source.type_word64, source.FunctionName(
                            "(_ zero_extend 32)"), [idx])
                    ),
                    source.ExprFunction(
                        source.type_word64, lc_unhandled_notified, [lc_progvar]),
                ),
                ule(
                    idx,
                    u32(63)
                ),
                eq(
                    u64(0),
                    source.expr_shift_right(
                        source.ExprFunction(
                            source.type_word64, lc_unhandled_notified, [lc_progvar]),
                        i64(63)
                    )
                ),
                eq(
                    u64(0),
                    source.expr_shift_right(
                        lbadge,
                        u64(63)
                    )
                ),
                eq(
                    source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"), [
                        source.ExprFunction(
                            source.type_word64, lc_unhandled_notified, [lc_progvar]),
                        source.ExprFunction(
                            source.type_word64, lc_last_handled_notified, [lc_progvar])
                    ]),
                    source.ExprFunction(
                        source.type_word64, source.FunctionName("Ch_set_empty"), [])
                ),
                eq(
                    source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_union"), [
                        source.ExprFunction(
                            source.type_word64, lc_unhandled_notified, [lc_progvar]),
                        source.ExprFunction(
                            source.type_word64, lc_last_handled_notified, [lc_progvar])
                    ]),
                    source.ExprFunction(Set_Ch, NextRecvNotificationGet, [source.ExprFunction(
                        NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])])
                ),
                eq(
                    source.ExprFunction(
                        Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, []),
                    source.ExprFunction(
                        Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, [lc_progvar]),
                ),
                eq(
                    source.ExprFunction(Maybe_MsgInfo, source.FunctionName(
                        "handler_loop_pre_unhandled_reply"), []),
                    source.ExprFunction(
                        Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar]),
                ),
                eq(
                    source.ExprFunction(NextRecv, NR_Unknown, []),
                    source.ExprFunction(
                        NextRecv, lc_receive_oracle, [lc_progvar]),
                ),
            ),
        },
        loop_iterations={
            lh(handler_loop_node_name()): source.LoopIterationGhost(
                pre_iter=handler_loop_iter_pre(),
                post_iter=handler_loop_iter_post(),
            ),
            lh('10'): source.empty_loop_ghost,
        },
        precondition=T,
        postcondition=T)
}
