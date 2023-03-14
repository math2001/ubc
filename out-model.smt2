sat
sat
(
  ;; universe for HTD:
  ;;   HTD!val!0 HTD!val!2 HTD!val!1 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun HTD!val!0 () HTD)
  (declare-fun HTD!val!2 () HTD)
  (declare-fun HTD!val!1 () HTD)
  ;; cardinality constraint:
  (forall ((x HTD)) (or (= x HTD!val!0) (= x HTD!val!2) (= x HTD!val!1)))
  ;; -----------
  ;; universe for PMS:
  ;;   PMS!val!0 PMS!val!2 PMS!val!1 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun PMS!val!0 () PMS)
  (declare-fun PMS!val!2 () PMS)
  (declare-fun PMS!val!1 () PMS)
  ;; cardinality constraint:
  (forall ((x PMS)) (or (= x PMS!val!0) (= x PMS!val!2) (= x PMS!val!1)))
  ;; -----------
  (define-fun node_loop_10_inv_asm_2_ok () Bool
    true)
  (define-fun node_prove_guard_n16_16_ok () Bool
    true)
  (define-fun node_upd_n7_ok () Bool
    true)
  (define-fun node_upd_n35_ok () Bool
    false)
  (define-fun node_guard_n30_ok () Bool
    false)
  (define-fun node_32_ok () Bool
    true)
  (define-fun is_endpoint___unsigned_longlong@v@assigned~1 () Bool
    false)
  (define-fun PMS~3 () PMS
    PMS!val!0)
  (define-fun node_31_ok () Bool
    true)
  (define-fun node_15_ok () Bool
    true)
  (define-fun node_guard_n18_ok () Bool
    false)
  (define-fun Mem~6 () (Array (_ BitVec 61) (_ BitVec 64))
    ((as const (Array (_ BitVec 61) (_ BitVec 64))) #x0203010a00018840))
  (define-fun node_upd_n26_ok () Bool
    false)
  (define-fun node_19_ok () Bool
    false)
  (define-fun node_upd_n28_ok () Bool
    false)
  (define-fun badge___unsigned_longlong@v@assigned~4 () Bool
    true)
  (define-fun node_Ret_ok () Bool
    false)
  (define-fun node_guard_n33_ok () Bool
    false)
  (define-fun node_49_ok () Bool
    false)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    true)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0022000040008000)
  (define-fun node_28_ok () Bool
    false)
  (define-fun node_upd_n23_ok () Bool
    false)
  (define-fun node_2_ok () Bool
    false)
  (define-fun node_30_ok () Bool
    false)
  (define-fun GhostAssertions~3 () (Array (_ BitVec 50) (_ BitVec 32))
    ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x80028000))
  (define-fun node_guard_n21_ok () Bool
    true)
  (define-fun node_prove_guard_n31_31_ok () Bool
    true)
  (define-fun node_25_ok () Bool
    false)
  (define-fun node_guard_n28_ok () Bool
    false)
  (define-fun have_reply___char@v@assigned~1 () Bool
    false)
  (define-fun node_guard_n26_ok () Bool
    false)
  (define-fun node_guard_n17_ok () Bool
    true)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    true)
  (define-fun idx___unsigned@v@assigned~1 () Bool
    false)
  (define-fun node_guard_n7_ok () Bool
    true)
  (define-fun node_guard_n16_ok () Bool
    true)
  (define-fun node_upd_n6_ok () Bool
    true)
  (define-fun node_j2_ok () Bool
    true)
  (define-fun node_3_ok () Bool
    false)
  (define-fun node_guard_n13_ok () Bool
    true)
  (define-fun GhostAssertions@assigned~4 () Bool
    false)
  (define-fun Mem@assigned~4 () Bool
    false)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_upd_n19_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~4 () Bool
    true)
  (define-fun PMS@assigned~7 () Bool
    true)
  (define-fun node_upd_n36_ok () Bool
    false)
  (define-fun Mem@assigned~5 () Bool
    true)
  (define-fun node_j1_ok () Bool
    false)
  (define-fun node_14_ok () Bool
    true)
  (define-fun have_reply___char@v~1 () (_ BitVec 8)
    #x00)
  (define-fun HTD@assigned~4 () Bool
    false)
  (define-fun loop@9@count~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_26_ok () Bool
    false)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun node_12_ok () Bool
    false)
  (define-fun loop@2@count~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_guard_n6_ok () Bool
    true)
  (define-fun idx___unsigned@v~1 () (_ BitVec 64)
    #x0002000000000000)
  (define-fun have_reply___char@v@assigned~4 () Bool
    true)
  (define-fun loop@9@count~4 () (_ BitVec 64)
    #x0000000082000000)
  (define-fun loop@9@count@assigned~1 () Bool
    false)
  (define-fun idx___unsigned@v~5 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun HTD~6 () HTD
    HTD!val!2)
  (define-fun GhostAssertions@assigned~7 () Bool
    true)
  (define-fun GhostAssertions@assigned~3 () Bool
    true)
  (define-fun PMS~7 () PMS
    PMS!val!2)
  (define-fun node_35_ok () Bool
    false)
  (define-fun node_upd_n39_ok () Bool
    false)
  (define-fun is_endpoint___unsigned_longlong@v@assigned~3 () Bool
    true)
  (define-fun node_prove_guard_n21_21_ok () Bool
    true)
  (define-fun idx___unsigned@v@assigned~3 () Bool
    true)
  (define-fun node_j5_ok () Bool
    false)
  (define-fun node_8_ok () Bool
    true)
  (define-fun node_upd_n8_ok () Bool
    true)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 () Bool
    false)
  (define-fun have_reply___char@v~3 () (_ BitVec 8)
    #x00)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~5 () Bool
    true)
  (define-fun node_upd_n30_ok () Bool
    false)
  (define-fun node_21_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v@assigned~6 () Bool
    true)
  (define-fun Mem@assigned~3 () Bool
    true)
  (define-fun HTD@assigned~5 () Bool
    true)
  (define-fun loop@2@count~3 () (_ BitVec 64)
    #x401ffffdffedfe70)
  (define-fun node_20_ok () Bool
    false)
  (define-fun node_33_ok () Bool
    false)
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun node_upd_n33_ok () Bool
    false)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~3 () (_ BitVec 64)
    #x0000000020000000)
  (define-fun HTD~3 () HTD
    HTD!val!0)
  (define-fun node_upd_n14_ok () Bool
    true)
  (define-fun HTD@assigned~1 () Bool
    true)
  (define-fun GhostAssertions~5 () (Array (_ BitVec 50) (_ BitVec 32))
    ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x80028000))
  (define-fun loop@2@count@assigned~1 () Bool
    false)
  (define-fun badge___unsigned_longlong@v~5 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_7_ok () Bool
    true)
  (define-fun node_39_ok () Bool
    false)
  (define-fun HTD@assigned~3 () Bool
    true)
  (define-fun HTD~5 () HTD
    HTD!val!0)
  (define-fun node_pre_condition_ok () Bool
    false)
  (define-fun node_prove_guard_n7_7_ok () Bool
    true)
  (define-fun Mem~4 () (Array (_ BitVec 61) (_ BitVec 64))
    (store ((as const (Array (_ BitVec 61) (_ BitVec 64))) #xf4a4f690694a25a1)
       #b1000000000000000000000000000000000000000000000000000000000000
       #xc00892aa3868a900))
  (define-fun node_guard_n36_ok () Bool
    false)
  (define-fun node_assume_postcond_16_upd_n16_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_assume_postcond_7_upd_n7_ok () Bool
    true)
  (define-fun sel4cp_internal_badge () (_ BitVec 61)
    #b0000000000000000000000000000000000000000000000000000000000000)
  (define-fun loop@9@count~1 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun idx___unsigned@v~3 () (_ BitVec 64)
    #x0000000000000001)
  (define-fun PMS~5 () PMS
    PMS!val!0)
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool
    true)
  (define-fun Mem@assigned~2 () Bool
    true)
  (define-fun is_endpoint___unsigned_longlong@v~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_upd_n13_ok () Bool
    true)
  (define-fun node_guard_n38_ok () Bool
    false)
  (define-fun is_endpoint___unsigned_longlong@v~1 () (_ BitVec 64)
    #x0000000000000010)
  (define-fun GhostAssertions~7 () (Array (_ BitVec 50) (_ BitVec 32))
    ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x0021220f))
  (define-fun PMS@assigned~6 () Bool
    true)
  (define-fun PMS@assigned~1 () Bool
    true)
  (define-fun PMS@assigned~3 () Bool
    true)
  (define-fun idx___unsigned@v~4 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun PMS@assigned~5 () Bool
    true)
  (define-fun node_10_ok () Bool
    false)
  (define-fun node_assume_postcond_31_upd_n31_ok () Bool
    true)
  (define-fun node_guard_n11_ok () Bool
    false)
  (define-fun Mem@assigned~6 () Bool
    true)
  (define-fun node_9_ok () Bool
    true)
  (define-fun node_17_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v@assigned~5 () Bool
    true)
  (define-fun node_24_ok () Bool
    false)
  (define-fun GhostAssertions@assigned~6 () Bool
    true)
  (define-fun idx___unsigned@v@assigned~2 () Bool
    false)
  (define-fun node_loop_3_latch_1_ok () Bool
    false)
  (define-fun node_16_ok () Bool
    true)
  (define-fun HTD@assigned~6 () Bool
    true)
  (define-fun node_guard_n31_ok () Bool
    true)
  (define-fun loop@9@count~3 () (_ BitVec 64)
    #x0000000082000000)
  (define-fun Mem@assigned~1 () Bool
    true)
  (define-fun node_5_ok () Bool
    false)
  (define-fun HTD@assigned~7 () Bool
    true)
  (define-fun node_23_ok () Bool
    false)
  (define-fun node_6_ok () Bool
    true)
  (define-fun node_loop_10_inv_asm_1_ok () Bool
    false)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun GhostAssertions@assigned~5 () Bool
    true)
  (define-fun node_1_ok () Bool
    false)
  (define-fun PMS@assigned~4 () Bool
    true)
  (define-fun node_loop_10_latch_1_ok () Bool
    false)
  (define-fun node_guard_n25_ok () Bool
    false)
  (define-fun idx___unsigned@v~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun Mem~7 () (Array (_ BitVec 61) (_ BitVec 64))
    ((as const (Array (_ BitVec 61) (_ BitVec 64))) #x0203010a00018840))
  (define-fun node_guard_n14_ok () Bool
    true)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~4 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_34_ok () Bool
    false)
  (define-fun is_endpoint___unsigned_longlong@v@assigned~2 () Bool
    false)
  (define-fun badge___unsigned_longlong@v@assigned~1 () Bool
    false)
  (define-fun rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun node_11_ok () Bool
    false)
  (define-fun have_reply___char@v~2 () (_ BitVec 8)
    #x00)
  (define-fun node_38_ok () Bool
    false)
  (define-fun have_reply___char@v@assigned~2 () Bool
    true)
  (define-fun node_assume_postcond_21_upd_n21_ok () Bool
    true)
  (define-fun node_upd_n21_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v~3 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun GhostAssertions~6 () (Array (_ BitVec 50) (_ BitVec 32))
    ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x0021220f))
  (define-fun Mem~3 () (Array (_ BitVec 61) (_ BitVec 64))
    (store ((as const (Array (_ BitVec 61) (_ BitVec 64))) #x0000000000000000)
       #b1000000000000000000000000000000000000000000000000000000000000
       #x0d564055808740c6))
  (define-fun node_j3_ok () Bool
    true)
  (define-fun node_prove_guard_n36_36_ok () Bool
    false)
  (define-fun node_upd_n16_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v~4 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun HTD~7 () HTD
    HTD!val!2)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2 () Bool
    false)
  (define-fun node_36_ok () Bool
    false)
  (define-fun node_loop_3_inv_asm_1_ok () Bool
    false)
  (define-fun node_upd_n24_ok () Bool
    false)
  (define-fun node_13_ok () Bool
    true)
  (define-fun Mem~5 () (Array (_ BitVec 61) (_ BitVec 64))
    (store ((as const (Array (_ BitVec 61) (_ BitVec 64))) #x0000000000000000)
       #b1000000000000000000000000000000000000000000000000000000000000
       #x0d564055808740c6))
  (define-fun loop@2@count~2 () (_ BitVec 64)
    #x401ffffdffedfe6f)
  (define-fun GhostAssertions@assigned~1 () Bool
    true)
  (define-fun node_guard_n22_ok () Bool
    false)
  (define-fun HTD@assigned~2 () Bool
    true)
  (define-fun node_loop_10_latch_2_ok () Bool
    true)
  (define-fun node_j6_ok () Bool
    true)
  (define-fun node_loop_3_latch_2_ok () Bool
    false)
  (define-fun node_guard_n19_ok () Bool
    false)
  (define-fun node_guard_n35_ok () Bool
    false)
  (define-fun node_37_ok () Bool
    false)
  (define-fun have_reply___char@v@assigned~3 () Bool
    true)
  (define-fun PMS~6 () PMS
    PMS!val!2)
  (define-fun node_4_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~5 () Bool
    true)
  (define-fun PMS@assigned~2 () Bool
    true)
  (define-fun node_29_ok () Bool
    false)
  (define-fun tag___struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64)
    #x0000000000000000)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 () Bool
    false)
  (define-fun GhostAssertions~4 () (Array (_ BitVec 50) (_ BitVec 32))
    (store ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x3cf81faf)
       #b00000000000000000000000000000000000000000000000000
       #x3e16c410))
  (define-fun HTD~4 () HTD
    HTD!val!1)
  (define-fun node_j4_ok () Bool
    true)
  (define-fun node_27_ok () Bool
    false)
  (define-fun node_loop_3_inv_asm_2_ok () Bool
    true)
  (define-fun badge___unsigned_longlong@v@assigned~3 () Bool
    true)
  (define-fun GhostAssertions@assigned~2 () Bool
    true)
  (define-fun Mem@assigned~7 () Bool
    true)
  (define-fun node_18_ok () Bool
    false)
  (define-fun node_assume_postcond_36_upd_n36_ok () Bool
    false)
  (define-fun node_post_condition_ok () Bool
    false)
  (define-fun node_upd_n18_ok () Bool
    false)
  (define-fun node_upd_n31_ok () Bool
    true)
  (define-fun reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool
    false)
  (define-fun node_upd_n49_ok () Bool
    false)
  (define-fun PMS~4 () PMS
    PMS!val!1)
  (define-fun node_22_ok () Bool
    false)
  (define-fun idx___unsigned@v@assigned~6 () Bool
    true)
  (define-fun node_Err_ok_1 () Bool
    true)
  (define-fun node_Err_ok_30 () Bool
    true)
  (define-fun node_Err_ok_11 () Bool
    true)
  (define-fun node_Err_ok_5 () Bool
    true)
  (define-fun node_Err_ok_13 () Bool
    true)
  (define-fun node_Err_ok_14 () Bool
    true)
  (define-fun node_Err_ok_25 () Bool
    true)
  (define-fun node_Err_ok_24 () Bool
    true)
  (define-fun node_Err_ok_16 () Bool
    true)
  (define-fun node_Err_ok_8 () Bool
    true)
  (define-fun node_Err_ok_17 () Bool
    true)
  (define-fun node_Err_ok_28 () Bool
    true)
  (define-fun node_Err_ok_33 () Bool
    false)
  (define-fun node_Err_ok_21 () Bool
    true)
  (define-fun node_Err_ok_10 () Bool
    true)
  (define-fun node_Err_ok_4 () Bool
    true)
  (define-fun node_Err_ok_26 () Bool
    true)
  (define-fun node_Err_ok_18 () Bool
    true)
  (define-fun node_Err_ok_23 () Bool
    true)
  (define-fun node_Err_ok_2 () Bool
    true)
  (define-fun node_Err_ok_27 () Bool
    true)
  (define-fun node_Err_ok_3 () Bool
    true)
  (define-fun node_Err_ok_22 () Bool
    true)
  (define-fun node_Err_ok_19 () Bool
    true)
  (define-fun node_Err_ok_32 () Bool
    true)
  (define-fun node_Err_ok_29 () Bool
    true)
  (define-fun node_Err_ok_31 () Bool
    true)
  (define-fun node_Err_ok_0 () Bool
    true)
  (define-fun node_Err_ok_9 () Bool
    true)
  (define-fun node_Err_ok_6 () Bool
    true)
  (define-fun node_Err_ok_20 () Bool
    true)
  (define-fun node_Err_ok_7 () Bool
    true)
  (define-fun node_Err_ok_12 () Bool
    true)
  (define-fun node_Err_ok_15 () Bool
    true)
  (define-fun HTD~8 () HTD
    HTD!val!0)
  (define-fun PMS~8 () PMS
    PMS!val!0)
  (define-fun GhostAssertions@assigned~8 () Bool
    false)
  (define-fun PMS@assigned~8 () Bool
    false)
  (define-fun Mem@assigned~8 () Bool
    false)
  (define-fun GhostAssertions~8 () (Array (_ BitVec 50) (_ BitVec 32))
    ((as const (Array (_ BitVec 50) (_ BitVec 32))) #x00000000))
  (define-fun HTD@assigned~8 () Bool
    false)
  (define-fun Mem~8 () (Array (_ BitVec 61) (_ BitVec 64))
    ((as const (Array (_ BitVec 61) (_ BitVec 64))) #x0000000000000000))
  (define-fun k!15 ((x!0 (_ BitVec 61))) (_ BitVec 64)
    #x0203010a00018840)
  (define-fun k!11 ((x!0 (_ BitVec 50))) (_ BitVec 32)
    #x80028000)
  (define-fun k!12 ((x!0 (_ BitVec 50))) (_ BitVec 32)
    (ite (= x!0 #b00000000000000000000000000000000000000000000000000) #x3e16c410
      #x3cf81faf))
  (define-fun k!13 ((x!0 (_ BitVec 61))) (_ BitVec 64)
    (ite (= x!0 #b1000000000000000000000000000000000000000000000000000000000000)
      #xc00892aa3868a900
      #xf4a4f690694a25a1))
)
