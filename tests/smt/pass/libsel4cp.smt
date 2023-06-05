sat
sat
(
  (declare-fun PMS!val!1 () PMS)
  (declare-fun PMS!val!2 () PMS)
  (declare-fun PMS!val!0 () PMS)
  (declare-fun PMS!val!3 () PMS)
  (declare-fun PMS!val!4 () PMS)
  (forall ((x PMS))
          (or (= x PMS!val!1)
              (= x PMS!val!2)
              (= x PMS!val!0)
              (= x PMS!val!3)
              (= x PMS!val!4)))
  (declare-fun HTD!val!0 () HTD)
  (declare-fun HTD!val!2 () HTD)
  (declare-fun HTD!val!3 () HTD)
  (declare-fun HTD!val!1 () HTD)
  (forall ((x HTD))
          (or (= x HTD!val!0) (= x HTD!val!2) (= x HTD!val!3) (= x HTD!val!1)))
  (define-fun node_loop_10_inv_asm_2_ok () Bool
    true)
  (define-fun node_upd_n7_ok () Bool
    true)
  (define-fun node_call_pre_31_pred_1_ok () Bool
    true)
  (define-fun node_guard_n30_ok () Bool
    true)
  (define-fun node_32_ok () Bool
    false)
  (define-fun Mem~5 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun GhostAssertions~3 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun node_31_ok () Bool
    true)
  (define-fun node_15_ok () Bool
    true)
  (define-fun node_guard_n18_ok () Bool
    false)
  (define-fun HTD/call-arg~4 () HTD
    HTD!val!1)
  (define-fun test@ghost@assigned~1 () Bool
    true)
  (define-fun node_upd_n26_ok () Bool
    true)
  (define-fun node_19_ok () Bool
    false)
  (define-fun node_upd_n28_ok () Bool
    true)
  (define-fun node_49_ok () Bool
    false)
  (define-fun node_Ret_ok () Bool
    true)
  (define-fun node_guard_n33_ok () Bool
    true)
  (define-fun have_reply____Bool@v~3 () (_ BitVec 8)
    #x00)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    true)
  (define-fun ch___unsigned@v/call-arg~3 () (_ BitVec 32)
    #x00000000)
  (define-fun node_28_ok () Bool
    true)
  (define-fun node_upd_n23_ok () Bool
    false)
  (define-fun node_2_ok () Bool
    true)
  (define-fun node_30_ok () Bool
    true)
  (define-fun node_Err_ok () Bool
    false)
  (define-fun PMS~3 () PMS
    PMS!val!2)
  (define-fun test@ghost@assigned~3 () Bool
    true)
  (define-fun node_guard_n21_ok () Bool
    false)
  (define-fun idx___unsigned@v~5 () (_ BitVec 32)
    #x00000000)
  (define-fun node_25_ok () Bool
    true)
  (define-fun node_call_stash_16_pred_1_ok () Bool
    true)
  (define-fun PMS/subject-arg~1 () PMS
    PMS!val!0)
  (define-fun node_guard_n28_ok () Bool
    true)
  (define-fun node_guard_n26_ok () Bool
    true)
  (define-fun node_guard_n17_ok () Bool
    false)
  (define-fun have_reply____Bool@v@assigned~3 () Bool
    false)
  (define-fun MEM@assigned~1 () Bool
    true)
  (define-fun idx___unsigned@v@assigned~1 () Bool
    false)
  (define-fun node_guard_n7_ok () Bool
    true)
  (define-fun lbadge___unsigned_long@v~2 () (_ BitVec 64)
    #x0000000000000001)
  (define-fun node_guard_n16_ok () Bool
    false)
  (define-fun node_upd_n6_ok () Bool
    true)
  (define-fun node_j2_ok () Bool
    true)
  (define-fun node_call_stash_21_pred_1_ok () Bool
    true)
  (define-fun node_3_ok () Bool
    false)
  (define-fun node_guard_n13_ok () Bool
    false)
  (define-fun test@ghost~5 () (_ BitVec 32)
    #x00000000)
  (define-fun Mem@assigned~4 () Bool
    false)
  (define-fun HTD/call-arg~3 () HTD
    HTD!val!3)
  (define-fun node_upd_n19_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~4 () Bool
    true)
  (define-fun is_endpoint@assigned~1 () Bool
    false)
  (define-fun lbadge___unsigned_long@v@assigned~3 () Bool
    true)
  (define-fun Mem@assigned~5 () Bool
    true)
  (define-fun PMS@assigned~7 () Bool
    true)
  (define-fun node_j1_ok () Bool
    true)
  (define-fun node_14_ok () Bool
    true)
  (define-fun node_call_stash_7_pred_1_ok () Bool
    true)
  (define-fun Mem~1 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun badge@global-symbol () (_ BitVec 64)
    #xfbf7fdffff7f7fa0)
  (define-fun test@ghost/call-arg~4 () (_ BitVec 32)
    #x00000000)
  (define-fun loop@9@count~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_26_ok () Bool
    true)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun GhostAssertions~1 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun node_j8_ok () Bool
    true)
  (define-fun node_12_ok () Bool
    false)
  (define-fun loop@2@count~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_guard_n6_ok () Bool
    true)
  (define-fun is_endpoint___unsigned_long@v~2 () (_ BitVec 64)
    #x0000020000000000)
  (define-fun loop@9@count~4 () (_ BitVec 64)
    #xaefc26e14699cc56)
  (define-fun node_upd_n37_ok () Bool
    false)
  (define-fun loop@9@count@assigned~1 () Bool
    false)
  (define-fun node_call_pre_21_pred_1_ok () Bool
    true)
  (define-fun GhostAssertions@assigned~7 () Bool
    true)
  (define-fun GhostAssertions@assigned~3 () Bool
    true)
  (define-fun PMS/call-arg~5 () PMS
    PMS!val!3)
  (define-fun node_35_ok () Bool
    true)
  (define-fun node_j5_ok () Bool
    true)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 () Bool
    true)
  (define-fun idx___unsigned@v@assigned~3 () Bool
    false)
  (define-fun node_upd_n8_ok () Bool
    true)
  (define-fun node_8_ok () Bool
    true)
  (define-fun node_upd_n30_ok () Bool
    true)
  (define-fun node_21_ok () Bool
    true)
  (define-fun GhostAssertions~5 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun node_call_stash_34_pred_1_ok () Bool
    true)
  (define-fun HTD/subject-arg~1 () HTD
    HTD!val!0)
  (define-fun lbadge___unsigned_long@v@assigned~6 () Bool
    true)
  (define-fun Mem/subject-arg~1 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun Mem@assigned~3 () Bool
    true)
  (define-fun HTD@assigned~5 () Bool
    true)
  (define-fun have_reply____Bool@v~1 () (_ BitVec 8)
    #x00)
  (define-fun node_20_ok () Bool
    false)
  (define-fun have_reply____Bool@v@assigned~1 () Bool
    false)
  (define-fun node_33_ok () Bool
    true)
  (define-fun idx___unsigned@v~3 () (_ BitVec 32)
    #x80100888)
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun node_upd_n33_ok () Bool
    true)
  (define-fun Mem/call-arg~4 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun HTD~3 () HTD
    HTD!val!2)
  (define-fun node_upd_n14_ok () Bool
    false)
  (define-fun HTD@assigned~1 () Bool
    true)
  (define-fun loop@2@count@assigned~1 () Bool
    false)
  (define-fun have_reply____Bool@v~2 () (_ BitVec 8)
    #x80)
  (define-fun lbadge___unsigned_long@v~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun HTD/call-arg~2 () HTD
    HTD!val!1)
  (define-fun node_call_post_16_ok () Bool
    true)
  (define-fun node_7_ok () Bool
    true)
  (define-fun idx___unsigned@v~4 () (_ BitVec 32)
    #x33adaa7d)
  (define-fun node_call_post_34_ok () Bool
    true)
  (define-fun ch___unsigned@v/call-arg~1 () (_ BitVec 32)
    #x00000000)
  (define-fun node_call_post_31_ok () Bool
    true)
  (define-fun test@ghost@assigned~5 () Bool
    true)
  (define-fun HTD@assigned~3 () Bool
    true)
  (define-fun HTD~5 () HTD
    HTD!val!2)
  (define-fun node_call_post_21_ok () Bool
    true)
  (define-fun node_pre_condition_ok () Bool
    false)
  (define-fun is_endpoint___unsigned_long@v@assigned~1 () Bool
    false)
  (define-fun node_guard_n36_ok () Bool
    false)
  (define-fun node_guard_n34_ok () Bool
    true)
  (define-fun GhostAssertions/subject-arg~1 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun HTD~1 () HTD
    HTD!val!0)
  (define-fun idx___unsigned@v~2 () (_ BitVec 32)
    #xa4b2afe8)
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    true)
  (define-fun Mem@assigned~2 () Bool
    true)
  (define-fun node_upd_n13_ok () Bool
    true)
  (define-fun node_call_pre_7_pred_1_ok () Bool
    true)
  (define-fun PMS@assigned~6 () Bool
    false)
  (define-fun lbadge___unsigned_long@v@assigned~1 () Bool
    false)
  (define-fun PMS@assigned~1 () Bool
    true)
  (define-fun PMS@assigned~3 () Bool
    true)
  (define-fun PMS@assigned~5 () Bool
    true)
  (define-fun node_10_ok () Bool
    true)
  (define-fun node_guard_n11_ok () Bool
    false)
  (define-fun badge@assigned~1 () Bool
    false)
  (define-fun node_9_ok () Bool
    false)
  (define-fun node_17_ok () Bool
    false)
  (define-fun PMS~5 () PMS
    PMS!val!2)
  (define-fun node_call_stash_31_pred_1_ok () Bool
    true)
  (define-fun node_24_ok () Bool
    true)
  (define-fun PMS~1 () PMS
    PMS!val!0)
  (define-fun loop@9@count~3 () (_ BitVec 64)
    #xaefc26e14699cc55)
  (define-fun node_loop_3_latch_1_ok () Bool
    false)
  (define-fun node_16_ok () Bool
    true)
  (define-fun node_guard_n31_ok () Bool
    false)
  (define-fun node_5_ok () Bool
    false)
  (define-fun Mem@assigned~1 () Bool
    true)
  (define-fun HTD@assigned~7 () Bool
    true)
  (define-fun node_23_ok () Bool
    false)
  (define-fun node_6_ok () Bool
    true)
  (define-fun node_loop_10_inv_asm_1_ok () Bool
    true)
  (define-fun node_j7_ok () Bool
    true)
  (define-fun GhostAssertions@assigned~5 () Bool
    true)
  (define-fun node_1_ok () Bool
    true)
  (define-fun node_loop_10_latch_1_ok () Bool
    false)
  (define-fun node_guard_n25_ok () Bool
    false)
  (define-fun node_guard_n14_ok () Bool
    true)
  (define-fun node_call_pre_34_pred_1_ok () Bool
    true)
  (define-fun node_34_ok () Bool
    true)
  (define-fun node_11_ok () Bool
    false)
  (define-fun test@ghost~3 () (_ BitVec 32)
    #x00000000)
  (define-fun node_call_post_7_ok () Bool
    true)
  (define-fun node_upd_n21_ok () Bool
    true)
  (define-fun node_j3_ok () Bool
    false)
  (define-fun node_call_pre_16_pred_1_ok () Bool
    true)
  (define-fun node_upd_n16_ok () Bool
    true)
  (define-fun node_36_ok () Bool
    false)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2 () Bool
    false)
  (define-fun node_loop_3_inv_asm_1_ok () Bool
    false)
  (define-fun node_upd_n24_ok () Bool
    true)
  (define-fun node_13_ok () Bool
    true)
  (define-fun loop@2@count~2 () (_ BitVec 64)
    #xfffffbfffffeffc6)
  (define-fun PMS/call-arg~4 () PMS
    PMS!val!1)
  (define-fun test@ghost~1 () (_ BitVec 32)
    #x00000000)
  (define-fun node_upd_n34_ok () Bool
    true)
  (define-fun GhostAssertions@assigned~1 () Bool
    true)
  (define-fun node_guard_n22_ok () Bool
    false)
  (define-fun HTD@assigned~2 () Bool
    true)
  (define-fun GhostAssertions/call-arg~2 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun node_j6_ok () Bool
    true)
  (define-fun node_loop_10_latch_2_ok () Bool
    false)
  (define-fun node_loop_3_latch_2_ok () Bool
    true)
  (define-fun node_guard_n19_ok () Bool
    false)
  (define-fun test@ghost/subject-arg~1 () (_ BitVec 32)
    #x00000000)
  (define-fun PMS/call-arg~2 () PMS
    PMS!val!1)
  (define-fun Mem/call-arg~2 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun lbadge___unsigned_long@v~4 () (_ BitVec 64)
    #x161882002d094101)
  (define-fun node_37_ok () Bool
    false)
  (define-fun PMS/call-arg~7 () PMS
    PMS!val!4)
  (define-fun have_reply____Bool@v@assigned~2 () Bool
    true)
  (define-fun have_reply@assigned~1 () Bool
    true)
  (define-fun test@ghost/call-arg~2 () (_ BitVec 32)
    #x00000000)
  (define-fun node_4_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~5 () Bool
    false)
  (define-fun PMS@assigned~2 () Bool
    true)
  (define-fun node_29_ok () Bool
    true)
  (define-fun lbadge___unsigned_long@v@assigned~5 () Bool
    true)
  (define-fun GhostAssertions/call-arg~4 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #xfbf7fdffff7f7fa0))
  (define-fun node_j4_ok () Bool
    true)
  (define-fun node_27_ok () Bool
    true)
  (define-fun node_loop_3_inv_asm_2_ok () Bool
    false)
  (define-fun have_reply____Bool@v@assigned~4 () Bool
    true)
  (define-fun test@ghost@assigned~2 () Bool
    true)
  (define-fun GhostAssertions@assigned~2 () Bool
    true)
  (define-fun node_18_ok () Bool
    true)
  (define-fun node_stash_initial_args_ok () Bool
    false)
  (define-fun node_post_condition_ok () Bool
    true)
  (define-fun is_endpoint___unsigned_long@v@assigned~3 () Bool
    false)
  (define-fun node_upd_n18_ok () Bool
    true)
  (define-fun Mem~3 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun node_upd_n31_ok () Bool
    true)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun node_upd_n49_ok () Bool
    false)
  (define-fun lbadge___unsigned_long@v~5 () (_ BitVec 64)
    #x0400b02001010020)
  (define-fun lbadge___unsigned_long@v@assigned~4 () Bool
    true)
  (define-fun node_22_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~6 () Bool
    true)
  (define-fun have_reply~1 () (_ BitVec 8)
    #x00)
  (define-fun test@ghost@assigned~7 () Bool
    false)
  (define-fun HTD~8 () HTD
    HTD!val!0)
  (define-fun ch___unsigned@v/call-arg~5 () (_ BitVec 32)
    #x00000000)
  (define-fun test@ghost~6 () (_ BitVec 32)
    #x00000000)
  (define-fun Mem/call-arg~3 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun ch___unsigned@v/call-arg~6 () (_ BitVec 32)
    #x00000000)
  (define-fun idx___unsigned@v@assigned~2 () Bool
    false)
  (define-fun Mem~4 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun test@ghost~8 () (_ BitVec 32)
    #x00000000)
  (define-fun msginfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem/call-arg~5 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun PMS~8 () PMS
    PMS!val!1)
  (define-fun msginfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~5 () Bool
    false)
  (define-fun msgInfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun PMS~7 () PMS
    PMS!val!1)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun is_endpoint___long@v~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem/call-arg~7 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun test@ghost~4 () (_ BitVec 32)
    #x00000000)
  (define-fun loop@9@count~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun GhostAssertions@assigned~8 () Bool
    false)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~4 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun msgInfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun test@ghost/call-arg~3 () (_ BitVec 32)
    #x00000000)
  (define-fun test@ghost~7 () (_ BitVec 32)
    #x00000000)
  (define-fun loop@2@count~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem~6 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun PMS@assigned~8 () Bool
    false)
  (define-fun Mem@assigned~6 () Bool
    false)
  (define-fun test@ghost/call-arg~6 () (_ BitVec 32)
    #x00000000)
  (define-fun reply_tag@assigned~1 () Bool
    false)
  (define-fun msgInfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun PMS/call-arg~6 () PMS
    PMS!val!1)
  (define-fun ch___unsigned@v/call-arg~2 () (_ BitVec 32)
    #x00000000)
  (define-fun GhostAssertions@assigned~4 () Bool
    false)
  (define-fun GhostAssertions/call-arg~5 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun msginfo___struct_seL4_MessageInfo_C@v.words_C.0/call-arg~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun HTD~4 () HTD
    HTD!val!0)
  (define-fun idx@assigned~1 () Bool
    false)
  (define-fun HTD@assigned~6 () Bool
    false)
  (define-fun HTD/call-arg~6 () HTD
    HTD!val!0)
  (define-fun test@ghost@assigned~4 () Bool
    false)
  (define-fun Mem@assigned~8 () Bool
    false)
  (define-fun GhostAssertions~6 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun PMS~6 () PMS
    PMS!val!1)
  (define-fun GhostAssertions~4 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun PMS~2 () PMS
    PMS!val!1)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    false)
  (define-fun idx___unsigned@v~1 () (_ BitVec 32)
    #x00000000)
  (define-fun test@ghost@assigned~8 () Bool
    false)
  (define-fun Mem~2 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun test@ghost/call-arg~7 () (_ BitVec 32)
    #x00000000)
  (define-fun GhostAssertions~7 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun test@ghost@assigned~6 () Bool
    false)
  (define-fun sender___ptr_to_unsigned_long@v/call-arg~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun GhostAssertions/call-arg~7 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun PMS/call-arg~3 () PMS
    PMS!val!1)
  (define-fun PMS@assigned~4 () Bool
    false)
  (define-fun HTD~2 () HTD
    HTD!val!0)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 () Bool
    false)
  (define-fun HTD/call-arg~7 () HTD
    HTD!val!0)
  (define-fun HTD/call-arg~5 () HTD
    HTD!val!0)
  (define-fun HTD~7 () HTD
    HTD!val!0)
  (define-fun GhostAssertions~8 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun GhostAssertions/call-arg~6 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun HTD@assigned~8 () Bool
    false)
  (define-fun Mem/call-arg~6 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun test@ghost/call-arg~5 () (_ BitVec 32)
    #x00000000)
  (define-fun GhostAssertions~2 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem@assigned~7 () Bool
    false)
  (define-fun ch___unsigned@v/call-arg~4 () (_ BitVec 32)
    #x00000000)
  (define-fun Mem~7 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun HTD@assigned~4 () Bool
    false)
  (define-fun PMS~4 () PMS
    PMS!val!1)
  (define-fun test@ghost~2 () (_ BitVec 32)
    #x00000000)
  (define-fun src___unsigned_long@v/call-arg~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem~8 () (Array (_ BitVec 64) (_ BitVec 8))
    ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
  (define-fun GhostAssertions@assigned~6 () Bool
    false)
  (define-fun HTD~6 () HTD
    HTD!val!0)
  (define-fun GhostAssertions/call-arg~3 () (Array (_ BitVec 50) (_ BitVec 64))
    ((as const (Array (_ BitVec 50) (_ BitVec 64))) #x0000000000000000))
)
