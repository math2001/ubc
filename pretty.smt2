(set-logic QF_ABV)
(declare-sort PMS 0)
(declare-sort HTD 0)
(define-fun
  mem-acc
  ((mem (Array (_ BitVec 61) (_ BitVec 64))) (addr (_ BitVec 61)))
  (_ BitVec 64)
  (select mem addr))
(declare-fun sel4cp_internal_badge () (_ BitVec 61))
(declare-fun node_Ret_ok () Bool)
(declare-fun node_49_ok () Bool)
(declare-fun node_pre_condition_ok () Bool)
(declare-fun node_upd_n49_ok () Bool)
(declare-fun node_39_ok () Bool)
(declare-fun node_upd_n39_ok () Bool)
(declare-fun node_5_ok () Bool)
(declare-fun node_loop_3_latch_1_ok () Bool)
(declare-fun node_3_ok () Bool)
(declare-fun node_loop_3_inv_asm_2_ok () Bool)
(declare-fun node_loop_3_inv_asm_1_ok () Bool)
(declare-fun node_4_ok () Bool)
(declare-fun node_1_ok () Bool)
(declare-fun node_post_condition_ok () Bool)
(declare-fun node_guard_n38_ok () Bool)
(declare-fun node_38_ok () Bool)
(declare-fun node_37_ok () Bool)
(declare-fun node_guard_n36_ok () Bool)
(declare-fun node_prove_guard_n36_36_ok () Bool)
(declare-fun node_36_ok () Bool)
(declare-fun node_assume_postcond_36_upd_n36_ok () Bool)
(declare-fun node_upd_n36_ok () Bool)
(declare-fun node_guard_n35_ok () Bool)
(declare-fun node_35_ok () Bool)
(declare-fun node_upd_n35_ok () Bool)
(declare-fun node_34_ok () Bool)
(declare-fun node_guard_n33_ok () Bool)
(declare-fun node_33_ok () Bool)
(declare-fun node_upd_n33_ok () Bool)
(declare-fun node_32_ok () Bool)
(declare-fun node_guard_n31_ok () Bool)
(declare-fun node_prove_guard_n31_31_ok () Bool)
(declare-fun node_31_ok () Bool)
(declare-fun node_assume_postcond_31_upd_n31_ok () Bool)
(declare-fun node_upd_n31_ok () Bool)
(declare-fun node_guard_n30_ok () Bool)
(declare-fun node_30_ok () Bool)
(declare-fun node_upd_n30_ok () Bool)
(declare-fun node_29_ok () Bool)
(declare-fun node_guard_n28_ok () Bool)
(declare-fun node_28_ok () Bool)
(declare-fun node_upd_n28_ok () Bool)
(declare-fun node_27_ok () Bool)
(declare-fun node_guard_n26_ok () Bool)
(declare-fun node_26_ok () Bool)
(declare-fun node_upd_n26_ok () Bool)
(declare-fun node_guard_n25_ok () Bool)
(declare-fun node_25_ok () Bool)
(declare-fun node_24_ok () Bool)
(declare-fun node_upd_n24_ok () Bool)
(declare-fun node_23_ok () Bool)
(declare-fun node_upd_n23_ok () Bool)
(declare-fun node_guard_n22_ok () Bool)
(declare-fun node_22_ok () Bool)
(declare-fun node_j1_ok () Bool)
(declare-fun node_guard_n21_ok () Bool)
(declare-fun node_prove_guard_n21_21_ok () Bool)
(declare-fun node_21_ok () Bool)
(declare-fun node_assume_postcond_21_upd_n21_ok () Bool)
(declare-fun node_upd_n21_ok () Bool)
(declare-fun node_j2_ok () Bool)
(declare-fun node_20_ok () Bool)
(declare-fun node_guard_n19_ok () Bool)
(declare-fun node_19_ok () Bool)
(declare-fun node_upd_n19_ok () Bool)
(declare-fun node_guard_n18_ok () Bool)
(declare-fun node_18_ok () Bool)
(declare-fun node_upd_n18_ok () Bool)
(declare-fun node_12_ok () Bool)
(declare-fun node_loop_10_latch_1_ok () Bool)
(declare-fun node_10_ok () Bool)
(declare-fun node_loop_10_inv_asm_2_ok () Bool)
(declare-fun node_loop_10_inv_asm_1_ok () Bool)
(declare-fun node_guard_n11_ok () Bool)
(declare-fun node_11_ok () Bool)
(declare-fun node_j5_ok () Bool)
(declare-fun node_guard_n17_ok () Bool)
(declare-fun node_17_ok () Bool)
(declare-fun node_j3_ok () Bool)
(declare-fun node_guard_n16_ok () Bool)
(declare-fun node_prove_guard_n16_16_ok () Bool)
(declare-fun node_16_ok () Bool)
(declare-fun node_assume_postcond_16_upd_n16_ok () Bool)
(declare-fun node_upd_n16_ok () Bool)
(declare-fun node_j4_ok () Bool)
(declare-fun node_15_ok () Bool)
(declare-fun node_guard_n14_ok () Bool)
(declare-fun node_14_ok () Bool)
(declare-fun node_upd_n14_ok () Bool)
(declare-fun node_guard_n13_ok () Bool)
(declare-fun node_13_ok () Bool)
(declare-fun node_upd_n13_ok () Bool)
(declare-fun node_9_ok () Bool)
(declare-fun node_loop_10_latch_2_ok () Bool)
(declare-fun node_8_ok () Bool)
(declare-fun node_upd_n8_ok () Bool)
(declare-fun node_guard_n7_ok () Bool)
(declare-fun node_prove_guard_n7_7_ok () Bool)
(declare-fun node_7_ok () Bool)
(declare-fun node_assume_postcond_7_upd_n7_ok () Bool)
(declare-fun node_upd_n7_ok () Bool)
(declare-fun node_guard_n6_ok () Bool)
(declare-fun node_6_ok () Bool)
(declare-fun node_upd_n6_ok () Bool)
(declare-fun node_j6_ok () Bool)
(declare-fun node_2_ok () Bool)
(declare-fun node_loop_3_latch_2_ok () Bool)

(declare-fun Mem@assigned~1 () Bool)
(declare-fun HTD@assigned~1 () Bool)
(declare-fun PMS@assigned~1 () Bool)
(declare-fun GhostAssertions@assigned~1 () Bool)
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~1
  ()
  Bool)
(declare-fun badge___unsigned_longlong@v@assigned~1 () Bool)
(declare-fun loop@2@count@assigned~1 () Bool)
(declare-fun idx___unsigned@v@assigned~1 () Bool)
(declare-fun have_reply___char@v@assigned~1 () Bool)
(declare-fun loop@9@count@assigned~1 () Bool)
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1
  ()
  Bool)
(declare-fun is_endpoint___unsigned_longlong@v@assigned~1 () Bool)
(declare-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 () Bool)
(declare-fun have_reply___char@v~1 () (_ BitVec 8))
(declare-fun have_reply___char@v@assigned~2 () Bool)
(declare-fun loop@2@count~1 () (_ BitVec 64))
(declare-fun is_endpoint___unsigned_longlong@v~1 () (_ BitVec 64))
(declare-fun PMS@assigned~2 () Bool)
(declare-fun have_reply___char@v~2 () (_ BitVec 8))
(declare-fun have_reply___char@v@assigned~3 () Bool)
(declare-fun GhostAssertions@assigned~2 () Bool)
(declare-fun Mem@assigned~2 () Bool)
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
  ()
  Bool)
(declare-fun HTD@assigned~2 () Bool)
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
  ()
  Bool)
(declare-fun Mem@assigned~3 () Bool)
(declare-fun HTD@assigned~3 () Bool)
(declare-fun PMS@assigned~3 () Bool)
(declare-fun GhostAssertions@assigned~3 () Bool)
(declare-fun tag___struct_seL4_MessageInfo_C@v.words_C.0~2 () (_ BitVec 64))
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2
  ()
  (_ BitVec 64))
(declare-fun tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 () Bool)
(declare-fun Mem~3 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun badge___unsigned_longlong@v~2 () (_ BitVec 64))
(declare-fun badge___unsigned_longlong@v@assigned~3 () Bool)
(declare-fun is_endpoint___unsigned_longlong@v~2 () (_ BitVec 64))
(declare-fun is_endpoint___unsigned_longlong@v@assigned~3 () Bool)
(declare-fun idx___unsigned@v~2 () (_ BitVec 64))
(declare-fun idx___unsigned@v@assigned~3 () Bool)
(declare-fun have_reply___char@v~3 () (_ BitVec 8))
(declare-fun have_reply___char@v@assigned~4 () Bool)
(declare-fun PMS~3 () PMS)
(declare-fun PMS~5 () PMS)
(declare-fun Mem~5 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun HTD@assigned~5 () Bool)
(declare-fun GhostAssertions~5 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun GhostAssertions~3 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun PMS@assigned~5 () Bool)
(declare-fun GhostAssertions@assigned~5 () Bool)
(declare-fun HTD~3 () HTD)
(declare-fun HTD~5 () HTD)
(declare-fun Mem@assigned~5 () Bool)
(declare-fun Mem@assigned~4 () Bool)
(declare-fun HTD@assigned~4 () Bool)
(declare-fun PMS@assigned~4 () Bool)
(declare-fun GhostAssertions@assigned~4 () Bool)
(declare-fun PMS~4 () PMS)
(declare-fun Mem~4 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun GhostAssertions~4 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun HTD~4 () HTD)
(declare-fun badge___unsigned_longlong@v~3 () (_ BitVec 64))
(declare-fun badge___unsigned_longlong@v@assigned~4 () Bool)
(declare-fun idx___unsigned@v~3 () (_ BitVec 64))
(declare-fun idx___unsigned@v@assigned~4 () Bool)
(declare-fun loop@9@count~2 () (_ BitVec 64))
(declare-fun HTD@assigned~6 () Bool)
(declare-fun Mem@assigned~6 () Bool)
(declare-fun PMS@assigned~6 () Bool)
(declare-fun GhostAssertions@assigned~6 () Bool)
(declare-fun badge___unsigned_longlong@v@assigned~5 () Bool)
(declare-fun badge___unsigned_longlong@v~4 () (_ BitVec 64))
(declare-fun loop@9@count~3 () (_ BitVec 64))
(declare-fun loop@9@count~4 () (_ BitVec 64))
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~3
  ()
  (_ BitVec 64))
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~1
  ()
  (_ BitVec 64))
(declare-fun PMS~7 () PMS)
(declare-fun PMS~6 () PMS)
(declare-fun Mem~7 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun Mem~6 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~4
  ()
  (_ BitVec 64))
(declare-fun badge___unsigned_longlong@v~5 () (_ BitVec 64))
(declare-fun HTD@assigned~7 () Bool)
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~5
  ()
  Bool)
(declare-fun GhostAssertions~7 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun GhostAssertions~6 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun PMS@assigned~7 () Bool)
(declare-fun badge___unsigned_longlong@v@assigned~6 () Bool)
(declare-fun GhostAssertions@assigned~7 () Bool)
(declare-fun HTD~7 () HTD)
(declare-fun HTD~6 () HTD)
(declare-fun idx___unsigned@v@assigned~5 () Bool)
(declare-fun idx___unsigned@v@assigned~6 () Bool)
(declare-fun idx___unsigned@v~4 () (_ BitVec 64))
(declare-fun idx___unsigned@v~5 () (_ BitVec 64))
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4
  ()
  Bool)
(declare-fun Mem@assigned~7 () Bool)
(declare-fun PMS~8 () PMS)
(declare-fun Mem~8 () (Array (_ BitVec 61) (_ BitVec 64)))
(declare-fun HTD@assigned~8 () Bool)
(declare-fun GhostAssertions~8 () (Array (_ BitVec 50) (_ BitVec 32)))
(declare-fun PMS@assigned~8 () Bool)
(declare-fun GhostAssertions@assigned~8 () Bool)
(declare-fun HTD~8 () HTD)
(declare-fun Mem@assigned~8 () Bool)
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4
  ()
  Bool)
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~2
  ()
  (_ BitVec 64))
(declare-fun
  rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~3
  ()
  (_ BitVec 64))
(declare-fun
  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
  ()
  Bool)
(declare-fun loop@9@count~1 () (_ BitVec 64))
(declare-fun idx___unsigned@v@assigned~2 () Bool)
(declare-fun idx___unsigned@v~1 () (_ BitVec 64))
(declare-fun loop@2@count~3 () (_ BitVec 64))
(declare-fun loop@2@count~2 () (_ BitVec 64))
(define-fun node_Err_ok_0 () Bool false)
(define-fun node_Err_ok_1 () Bool false)
(define-fun node_Err_ok_2 () Bool false)
(define-fun node_Err_ok_3 () Bool false)
(define-fun node_Err_ok_4 () Bool false)
(define-fun node_Err_ok_5 () Bool false)
(define-fun node_Err_ok_6 () Bool false)
(define-fun node_Err_ok_7 () Bool false)
(define-fun node_Err_ok_8 () Bool false)
(define-fun node_Err_ok_9 () Bool false)
(define-fun node_Err_ok_10 () Bool false)
(define-fun node_Err_ok_11 () Bool false)
(define-fun node_Err_ok_12 () Bool false)
(define-fun node_Err_ok_13 () Bool false)
(define-fun node_Err_ok_14 () Bool false)
(define-fun node_Err_ok_15 () Bool false)
(define-fun node_Err_ok_16 () Bool false)
(define-fun node_Err_ok_17 () Bool false)
(define-fun node_Err_ok_18 () Bool false)
(define-fun node_Err_ok_19 () Bool false)
(define-fun node_Err_ok_20 () Bool false)
(define-fun node_Err_ok_21 () Bool false)
(define-fun node_Err_ok_22 () Bool false)
(define-fun node_Err_ok_23 () Bool false)
(define-fun node_Err_ok_24 () Bool false)
(define-fun node_Err_ok_25 () Bool false)
(define-fun node_Err_ok_26 () Bool false)
(define-fun node_Err_ok_27 () Bool false)
(define-fun node_Err_ok_28 () Bool false)
(define-fun node_Err_ok_29 () Bool false)
(define-fun node_Err_ok_30 () Bool false)
(define-fun node_Err_ok_31 () Bool false)
(define-fun node_Err_ok_32 () Bool false)
(define-fun node_Err_ok_33 () Bool false)

(assert (= node_Ret_ok false))
(assert (= node_49_ok node_pre_condition_ok))
(assert (= node_pre_condition_ok (=> true node_upd_n49_ok)))
(assert
  (=
    node_upd_n49_ok
    (=>
      (= Mem@assigned~1 true)
      (=>
        (= HTD@assigned~1 true)
        (=>
          (= PMS@assigned~1 true)
          (=>
            (= GhostAssertions@assigned~1 true)
            (=>
              (= rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 false)
              (=>
                (= badge___unsigned_longlong@v@assigned~1 false)
                (=>
                  (= loop@2@count@assigned~1 false)
                  (=>
                    (= idx___unsigned@v@assigned~1 false)
                    (=>
                      (= have_reply___char@v@assigned~1 false)
                      (=>
                        (= loop@9@count@assigned~1 false)
                        (=>
                          (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 false)
                          (=>
                            (= is_endpoint___unsigned_longlong@v@assigned~1 false)
                            (=>
                              (= tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 false)
                              node_39_ok)))))))))))))))
(assert
  (=
    node_39_ok
    (=> (= have_reply___char@v~1 ((_ extract 7 0) (_ bv0 64))) node_upd_n39_ok)))
(assert
  (= node_upd_n39_ok (=> (= have_reply___char@v@assigned~2 true) node_5_ok)))
(assert
  (= node_5_ok (=> (= loop@2@count~1 (_ bv0 64)) node_loop_3_latch_1_ok)))
(assert
  (=
    node_loop_3_latch_1_ok
    (and
      (=>
        (and
          (and
            (and
              (and
                (and
                  (and
                    (=
                      (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                      (not (= have_reply___char@v~1 (_ bv0 8))))
                    (=
                      (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                      (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 true)))
                  (= HTD@assigned~1 true))
                (= Mem@assigned~1 true))
              (= PMS@assigned~1 true))
            (= GhostAssertions@assigned~1 true))
          (= have_reply___char@v@assigned~2 true))
        node_3_ok)
      (=>
        (not
          (and
            (and
              (and
                (and
                  (and
                    (and
                      (=
                        (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                        (not (= have_reply___char@v~1 (_ bv0 8))))
                      (=
                        (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                        (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~1 true)))
                    (= HTD@assigned~1 true))
                  (= Mem@assigned~1 true))
                (= PMS@assigned~1 true))
              (= GhostAssertions@assigned~1 true))
            (= have_reply___char@v@assigned~2 true)))
        node_Err_ok_0))))
(assert
  (=
    node_3_ok
    (and (=> true node_loop_3_inv_asm_1_ok) (=> false node_loop_3_inv_asm_2_ok))))
(assert
  (=
    node_loop_3_inv_asm_2_ok
    (=>
      (and
        (and
          (and
            (and
              (and
                (and
                  (=
                    (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                    (not (= have_reply___char@v~2 (_ bv0 8))))
                  (=
                    (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                    (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2 true)))
                (= HTD@assigned~2 true))
              (= Mem@assigned~2 true))
            (= PMS@assigned~2 true))
          (= GhostAssertions@assigned~2 true))
        (= have_reply___char@v@assigned~3 true))
      node_Err_ok_1)))
(assert
  (=
    node_loop_3_inv_asm_1_ok
    (=>
      (and
        (and
          (and
            (and
              (and
                (and
                  (=
                    (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                    (not (= have_reply___char@v~2 (_ bv0 8))))
                  (=
                    (not (= is_endpoint___unsigned_longlong@v~1 (_ bv0 64)))
                    (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2 true)))
                (= HTD@assigned~2 true))
              (= Mem@assigned~2 true))
            (= PMS@assigned~2 true))
          (= GhostAssertions@assigned~2 true))
        (= have_reply___char@v@assigned~3 true))
      node_4_ok)))
(assert
  (=
    node_4_ok
    (and
      (=> (not (= (_ bv1 64) (_ bv0 64))) node_guard_n38_ok)
      (=> (= (_ bv1 64) (_ bv0 64)) node_1_ok))))
(assert (= node_1_ok node_post_condition_ok))
(assert
  (= node_post_condition_ok (and (=> true node_Ret_ok) (=> false node_Err_ok_2))))
(assert
  (=
    node_guard_n38_ok
    (and
      (=> have_reply___char@v@assigned~3 node_38_ok)
      (=> (not have_reply___char@v@assigned~3) node_Err_ok_3))))
(assert
  (=
    node_38_ok
    (and
      (=> (not (= have_reply___char@v~2 (_ bv0 8))) node_32_ok)
      (=> (= have_reply___char@v~2 (_ bv0 8)) node_37_ok))))
(assert
  (= node_37_ok (and (=> true node_guard_n36_ok) (=> (not true) node_Err_ok_4))))
(assert
  (=
    node_guard_n36_ok
    (and
      (=>
        (and
          (and (and PMS@assigned~2 Mem@assigned~2) GhostAssertions@assigned~2)
          HTD@assigned~2)
        node_prove_guard_n36_36_ok)
      (=>
        (not
          (and
            (and (and PMS@assigned~2 Mem@assigned~2) GhostAssertions@assigned~2)
            HTD@assigned~2))
        node_Err_ok_5))))
(assert (= node_prove_guard_n36_36_ok node_36_ok))
(assert (= node_36_ok node_assume_postcond_36_upd_n36_ok))
(assert (= node_assume_postcond_36_upd_n36_ok (=> true node_upd_n36_ok)))
(assert
  (=
    node_upd_n36_ok
    (=>
      (=
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
        (and
          (and (and Mem@assigned~2 HTD@assigned~2) PMS@assigned~2)
          GhostAssertions@assigned~2))
      (=>
        (=
          Mem@assigned~3
          (and
            (and (and Mem@assigned~2 HTD@assigned~2) PMS@assigned~2)
            GhostAssertions@assigned~2))
        (=>
          (=
            HTD@assigned~3
            (and
              (and (and Mem@assigned~2 HTD@assigned~2) PMS@assigned~2)
              GhostAssertions@assigned~2))
          (=>
            (=
              PMS@assigned~3
              (and
                (and (and Mem@assigned~2 HTD@assigned~2) PMS@assigned~2)
                GhostAssertions@assigned~2))
            (=>
              (=
                GhostAssertions@assigned~3
                (and
                  (and (and Mem@assigned~2 HTD@assigned~2) PMS@assigned~2)
                  GhostAssertions@assigned~2))
              node_guard_n35_ok)))))))
(assert
  (=
    node_guard_n35_ok
    (and
      (=> rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 node_35_ok)
      (=>
        (not rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
        node_Err_ok_6))))
(assert
  (=
    node_35_ok
    (=>
      (=
        tag___struct_seL4_MessageInfo_C@v.words_C.0~2
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2)
      node_upd_n35_ok)))
(assert
  (=
    node_upd_n35_ok
    (=>
      (=
        tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
      node_34_ok)))
(assert
  (= node_34_ok (and (=> true node_guard_n33_ok) (=> (not true) node_Err_ok_7))))
(assert
  (=
    node_guard_n33_ok
    (and (=> Mem@assigned~3 node_33_ok) (=> (not Mem@assigned~3) node_Err_ok_8))))
(assert
  (=
    node_33_ok
    (=>
      (= badge___unsigned_longlong@v~2 (mem-acc Mem~3 sel4cp_internal_badge))
      node_upd_n33_ok)))
(assert
  (=
    node_upd_n33_ok
    (=> (= badge___unsigned_longlong@v@assigned~3 Mem@assigned~3) node_27_ok)))
(assert
  (= node_32_ok (and (=> true node_guard_n31_ok) (=> (not true) node_Err_ok_9))))
(assert
  (=
    node_guard_n31_ok
    (and
      (=>
        (and
          (and
            (and
              (and
                Mem@assigned~2
                reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2)
              GhostAssertions@assigned~2)
            PMS@assigned~2)
          HTD@assigned~2)
        node_prove_guard_n31_31_ok)
      (=>
        (not
          (and
            (and
              (and
                (and
                  Mem@assigned~2
                  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2)
                GhostAssertions@assigned~2)
              PMS@assigned~2)
            HTD@assigned~2))
        node_Err_ok_10))))
(assert (= node_prove_guard_n31_31_ok node_31_ok))
(assert (= node_31_ok node_assume_postcond_31_upd_n31_ok))
(assert (= node_assume_postcond_31_upd_n31_ok (=> true node_upd_n31_ok)))
(assert
  (=
    node_upd_n31_ok
    (=>
      (=
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
        (and
          (and
            (and
              (and
                reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
                Mem@assigned~2)
              HTD@assigned~2)
            PMS@assigned~2)
          GhostAssertions@assigned~2))
      (=>
        (=
          Mem@assigned~3
          (and
            (and
              (and
                (and
                  reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
                  Mem@assigned~2)
                HTD@assigned~2)
              PMS@assigned~2)
            GhostAssertions@assigned~2))
        (=>
          (=
            HTD@assigned~3
            (and
              (and
                (and
                  (and
                    reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
                    Mem@assigned~2)
                  HTD@assigned~2)
                PMS@assigned~2)
              GhostAssertions@assigned~2))
          (=>
            (=
              PMS@assigned~3
              (and
                (and
                  (and
                    (and
                      reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
                      Mem@assigned~2)
                    HTD@assigned~2)
                  PMS@assigned~2)
                GhostAssertions@assigned~2))
            (=>
              (=
                GhostAssertions@assigned~3
                (and
                  (and
                    (and
                      (and
                        reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2
                        Mem@assigned~2)
                      HTD@assigned~2)
                    PMS@assigned~2)
                  GhostAssertions@assigned~2))
              node_guard_n30_ok)))))))
(assert
  (=
    node_guard_n30_ok
    (and
      (=> rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3 node_30_ok)
      (=>
        (not rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
        node_Err_ok_11))))
(assert
  (=
    node_30_ok
    (=>
      (=
        tag___struct_seL4_MessageInfo_C@v.words_C.0~2
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2)
      node_upd_n30_ok)))
(assert
  (=
    node_upd_n30_ok
    (=>
      (=
        tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
      node_29_ok)))
(assert
  (= node_29_ok (and (=> true node_guard_n28_ok) (=> (not true) node_Err_ok_12))))
(assert
  (=
    node_guard_n28_ok
    (and (=> Mem@assigned~3 node_28_ok) (=> (not Mem@assigned~3) node_Err_ok_13))))
(assert
  (=
    node_28_ok
    (=>
      (= badge___unsigned_longlong@v~2 (mem-acc Mem~3 sel4cp_internal_badge))
      node_upd_n28_ok)))
(assert
  (=
    node_upd_n28_ok
    (=> (= badge___unsigned_longlong@v@assigned~3 Mem@assigned~3) node_27_ok)))
(assert
  (=
    node_27_ok
    (and
      (=>
        (and (bvsle (_ bv0 64) (_ bv63 64)) (bvslt (_ bv63 64) (_ bv64 64)))
        node_guard_n26_ok)
      (=>
        (not (and (bvsle (_ bv0 64) (_ bv63 64)) (bvslt (_ bv63 64) (_ bv64 64))))
        node_Err_ok_14))))
(assert
  (=
    node_guard_n26_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~3 node_26_ok)
      (=> (not badge___unsigned_longlong@v@assigned~3) node_Err_ok_15))))
(assert
  (=
    node_26_ok
    (=>
      (=
        is_endpoint___unsigned_longlong@v~2
        (bvlshr badge___unsigned_longlong@v~2 (_ bv63 64)))
      node_upd_n26_ok)))
(assert
  (=
    node_upd_n26_ok
    (=>
      (=
        is_endpoint___unsigned_longlong@v@assigned~3
        badge___unsigned_longlong@v@assigned~3)
      node_guard_n25_ok)))
(assert
  (=
    node_guard_n25_ok
    (and
      (=> is_endpoint___unsigned_longlong@v@assigned~3 node_25_ok)
      (=> (not is_endpoint___unsigned_longlong@v@assigned~3) node_Err_ok_16))))
(assert
  (=
    node_25_ok
    (and
      (=> (not (= is_endpoint___unsigned_longlong@v~2 (_ bv0 64))) node_8_ok)
      (=> (= is_endpoint___unsigned_longlong@v~2 (_ bv0 64)) node_24_ok))))
(assert (= node_24_ok (=> (= idx___unsigned@v~2 (_ bv0 64)) node_upd_n24_ok)))
(assert
  (= node_upd_n24_ok (=> (= idx___unsigned@v@assigned~3 true) node_23_ok)))
(assert
  (=
    node_23_ok
    (=> (= have_reply___char@v~3 ((_ extract 7 0) (_ bv0 64))) node_upd_n23_ok)))
(assert
  (=
    node_upd_n23_ok
    (=> (= have_reply___char@v@assigned~4 true) node_guard_n22_ok)))
(assert
  (=
    node_guard_n22_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~3 node_22_ok)
      (=> (not badge___unsigned_longlong@v@assigned~3) node_Err_ok_17))))
(assert
  (=
    node_22_ok
    (and
      (=>
        (not (= (bvand badge___unsigned_longlong@v~2 (_ bv1 64)) (_ bv0 64)))
        node_guard_n21_ok)
      (=> (= (bvand badge___unsigned_longlong@v~2 (_ bv1 64)) (_ bv0 64)) node_j1_ok))))
(assert
  (=
    node_j1_ok
    (=>
      (= PMS~5 PMS~3)
      (=>
        (= Mem~5 Mem~3)
        (=>
          (= HTD@assigned~5 HTD@assigned~3)
          (=>
            (= GhostAssertions~5 GhostAssertions~3)
            (=>
              (= PMS@assigned~5 PMS@assigned~3)
              (=>
                (= GhostAssertions@assigned~5 GhostAssertions@assigned~3)
                (=> (= HTD~5 HTD~3) (=> (= Mem@assigned~5 Mem@assigned~3) node_20_ok))))))))))
(assert
  (=
    node_guard_n21_ok
    (and
      (=>
        (and
          (and
            (and
              (and Mem@assigned~3 idx___unsigned@v@assigned~3)
              GhostAssertions@assigned~3)
            PMS@assigned~3)
          HTD@assigned~3)
        node_prove_guard_n21_21_ok)
      (=>
        (not
          (and
            (and
              (and
                (and Mem@assigned~3 idx___unsigned@v@assigned~3)
                GhostAssertions@assigned~3)
              PMS@assigned~3)
            HTD@assigned~3))
        node_Err_ok_18))))
(assert (= node_prove_guard_n21_21_ok node_21_ok))
(assert (= node_21_ok node_assume_postcond_21_upd_n21_ok))
(assert (= node_assume_postcond_21_upd_n21_ok (=> true node_upd_n21_ok)))
(assert
  (=
    node_upd_n21_ok
    (=>
      (=
        Mem@assigned~4
        (and
          (and
            (and (and idx___unsigned@v@assigned~3 Mem@assigned~3) HTD@assigned~3)
            PMS@assigned~3)
          GhostAssertions@assigned~3))
      (=>
        (=
          HTD@assigned~4
          (and
            (and
              (and (and idx___unsigned@v@assigned~3 Mem@assigned~3) HTD@assigned~3)
              PMS@assigned~3)
            GhostAssertions@assigned~3))
        (=>
          (=
            PMS@assigned~4
            (and
              (and
                (and (and idx___unsigned@v@assigned~3 Mem@assigned~3) HTD@assigned~3)
                PMS@assigned~3)
              GhostAssertions@assigned~3))
          (=>
            (=
              GhostAssertions@assigned~4
              (and
                (and
                  (and (and idx___unsigned@v@assigned~3 Mem@assigned~3) HTD@assigned~3)
                  PMS@assigned~3)
                GhostAssertions@assigned~3))
            node_j2_ok))))))
(assert
  (=
    node_j2_ok
    (=>
      (= PMS~5 PMS~4)
      (=>
        (= Mem~5 Mem~4)
        (=>
          (= HTD@assigned~5 HTD@assigned~4)
          (=>
            (= GhostAssertions~5 GhostAssertions~4)
            (=>
              (= PMS@assigned~5 PMS@assigned~4)
              (=>
                (= GhostAssertions@assigned~5 GhostAssertions@assigned~4)
                (=> (= HTD~5 HTD~4) (=> (= Mem@assigned~5 Mem@assigned~4) node_20_ok))))))))))
(assert
  (=
    node_20_ok
    (and
      (=>
        (and (bvsle (_ bv0 64) (_ bv1 64)) (bvslt (_ bv1 64) (_ bv64 64)))
        node_guard_n19_ok)
      (=>
        (not (and (bvsle (_ bv0 64) (_ bv1 64)) (bvslt (_ bv1 64) (_ bv64 64))))
        node_Err_ok_19))))
(assert
  (=
    node_guard_n19_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~3 node_19_ok)
      (=> (not badge___unsigned_longlong@v@assigned~3) node_Err_ok_20))))
(assert
  (=
    node_19_ok
    (=>
      (=
        badge___unsigned_longlong@v~3
        (bvlshr badge___unsigned_longlong@v~2 (_ bv1 64)))
      node_upd_n19_ok)))
(assert
  (=
    node_upd_n19_ok
    (=>
      (=
        badge___unsigned_longlong@v@assigned~4
        badge___unsigned_longlong@v@assigned~3)
      node_guard_n18_ok)))
(assert
  (=
    node_guard_n18_ok
    (and
      (=> idx___unsigned@v@assigned~3 node_18_ok)
      (=> (not idx___unsigned@v@assigned~3) node_Err_ok_21))))
(assert
  (=
    node_18_ok
    (=>
      (= idx___unsigned@v~3 (bvadd idx___unsigned@v~2 (_ bv1 64)))
      node_upd_n18_ok)))
(assert
  (=
    node_upd_n18_ok
    (=> (= idx___unsigned@v@assigned~4 idx___unsigned@v@assigned~3) node_12_ok)))
(assert
  (= node_12_ok (=> (= loop@9@count~2 (_ bv0 64)) node_loop_10_latch_1_ok)))
(assert
  (=
    node_loop_10_latch_1_ok
    (and
      (=>
        (and
          (and
            (and (= HTD@assigned~5 true) (= Mem@assigned~5 true))
            (= PMS@assigned~5 true))
          (= GhostAssertions@assigned~5 true))
        node_10_ok)
      (=>
        (not
          (and
            (and
              (and (= HTD@assigned~5 true) (= Mem@assigned~5 true))
              (= PMS@assigned~5 true))
            (= GhostAssertions@assigned~5 true)))
        node_Err_ok_22))))
(assert
  (=
    node_10_ok
    (and (=> true node_loop_10_inv_asm_1_ok) (=> false node_loop_10_inv_asm_2_ok))))
(assert
  (=
    node_loop_10_inv_asm_2_ok
    (=>
      (and
        (and
          (and (= HTD@assigned~6 true) (= Mem@assigned~6 true))
          (= PMS@assigned~6 true))
        (= GhostAssertions@assigned~6 true))
      node_Err_ok_23)))
(assert
  (=
    node_loop_10_inv_asm_1_ok
    (=>
      (and
        (and
          (and (= HTD@assigned~6 true) (= Mem@assigned~6 true))
          (= PMS@assigned~6 true))
        (= GhostAssertions@assigned~6 true))
      node_guard_n11_ok)))
(assert
  (=
    node_guard_n11_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~5 node_11_ok)
      (=> (not badge___unsigned_longlong@v@assigned~5) node_Err_ok_24))))
(assert
  (=
    node_11_ok
    (and
      (=> (not (= badge___unsigned_longlong@v~4 (_ bv0 64))) node_guard_n17_ok)
      (=> (= badge___unsigned_longlong@v~4 (_ bv0 64)) node_j5_ok))))
(assert
  (=
    node_j5_ok
    (=>
      (= loop@9@count~4 loop@9@count~3)
      (=>
        (=
          reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~3
          reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~1)
        (=>
          (= PMS~7 PMS~6)
          (=>
            (= Mem~7 Mem~6)
            (=>
              (=
                rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~4
                rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~2)
              (=>
                (= badge___unsigned_longlong@v~5 badge___unsigned_longlong@v~4)
                (=>
                  (= HTD@assigned~7 HTD@assigned~6)
                  (=>
                    (=
                      rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~5
                      rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                    (=>
                      (= GhostAssertions~7 GhostAssertions~6)
                      (=>
                        (= PMS@assigned~7 PMS@assigned~6)
                        (=>
                          (=
                            badge___unsigned_longlong@v@assigned~6
                            badge___unsigned_longlong@v@assigned~5)
                          (=>
                            (= GhostAssertions@assigned~7 GhostAssertions@assigned~6)
                            (=>
                              (= HTD~7 HTD~6)
                              (=>
                                (= idx___unsigned@v@assigned~6 idx___unsigned@v@assigned~5)
                                (=>
                                  (= idx___unsigned@v~5 idx___unsigned@v~4)
                                  (=>
                                    (=
                                      reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4
                                      reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2)
                                    (=> (= Mem@assigned~7 Mem@assigned~6) node_2_ok)))))))))))))))))))
(assert
  (=
    node_guard_n17_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~5 node_17_ok)
      (=> (not badge___unsigned_longlong@v@assigned~5) node_Err_ok_25))))
(assert
  (=
    node_17_ok
    (and
      (=>
        (not (= (bvand badge___unsigned_longlong@v~4 (_ bv1 64)) (_ bv0 64)))
        node_guard_n16_ok)
      (=> (= (bvand badge___unsigned_longlong@v~4 (_ bv1 64)) (_ bv0 64)) node_j3_ok))))
(assert
  (=
    node_j3_ok
    (=>
      (= PMS~8 PMS~6)
      (=>
        (= Mem~8 Mem~6)
        (=>
          (= HTD@assigned~8 HTD@assigned~6)
          (=>
            (= GhostAssertions~8 GhostAssertions~6)
            (=>
              (= PMS@assigned~8 PMS@assigned~6)
              (=>
                (= GhostAssertions@assigned~8 GhostAssertions@assigned~6)
                (=> (= HTD~8 HTD~6) (=> (= Mem@assigned~8 Mem@assigned~6) node_15_ok))))))))))
(assert
  (=
    node_guard_n16_ok
    (and
      (=>
        (and
          (and
            (and
              (and Mem@assigned~6 idx___unsigned@v@assigned~5)
              GhostAssertions@assigned~6)
            PMS@assigned~6)
          HTD@assigned~6)
        node_prove_guard_n16_16_ok)
      (=>
        (not
          (and
            (and
              (and
                (and Mem@assigned~6 idx___unsigned@v@assigned~5)
                GhostAssertions@assigned~6)
              PMS@assigned~6)
            HTD@assigned~6))
        node_Err_ok_26))))
(assert (= node_prove_guard_n16_16_ok node_16_ok))
(assert (= node_16_ok node_assume_postcond_16_upd_n16_ok))
(assert (= node_assume_postcond_16_upd_n16_ok (=> true node_upd_n16_ok)))
(assert
  (=
    node_upd_n16_ok
    (=>
      (=
        Mem@assigned~7
        (and
          (and
            (and (and idx___unsigned@v@assigned~5 Mem@assigned~6) HTD@assigned~6)
            PMS@assigned~6)
          GhostAssertions@assigned~6))
      (=>
        (=
          HTD@assigned~7
          (and
            (and
              (and (and idx___unsigned@v@assigned~5 Mem@assigned~6) HTD@assigned~6)
              PMS@assigned~6)
            GhostAssertions@assigned~6))
        (=>
          (=
            PMS@assigned~7
            (and
              (and
                (and (and idx___unsigned@v@assigned~5 Mem@assigned~6) HTD@assigned~6)
                PMS@assigned~6)
              GhostAssertions@assigned~6))
          (=>
            (=
              GhostAssertions@assigned~7
              (and
                (and
                  (and (and idx___unsigned@v@assigned~5 Mem@assigned~6) HTD@assigned~6)
                  PMS@assigned~6)
                GhostAssertions@assigned~6))
            node_j4_ok))))))
(assert
  (=
    node_j4_ok
    (=>
      (= PMS~8 PMS~7)
      (=>
        (= Mem~8 Mem~7)
        (=>
          (= HTD@assigned~8 HTD@assigned~7)
          (=>
            (= GhostAssertions~8 GhostAssertions~7)
            (=>
              (= PMS@assigned~8 PMS@assigned~7)
              (=>
                (= GhostAssertions@assigned~8 GhostAssertions@assigned~7)
                (=> (= HTD~8 HTD~7) (=> (= Mem@assigned~8 Mem@assigned~7) node_15_ok))))))))))
(assert
  (=
    node_15_ok
    (and
      (=>
        (and (bvsle (_ bv0 64) (_ bv1 64)) (bvslt (_ bv1 64) (_ bv64 64)))
        node_guard_n14_ok)
      (=>
        (not (and (bvsle (_ bv0 64) (_ bv1 64)) (bvslt (_ bv1 64) (_ bv64 64))))
        node_Err_ok_27))))
(assert
  (=
    node_guard_n14_ok
    (and
      (=> badge___unsigned_longlong@v@assigned~5 node_14_ok)
      (=> (not badge___unsigned_longlong@v@assigned~5) node_Err_ok_28))))
(assert
  (=
    node_14_ok
    (=>
      (=
        badge___unsigned_longlong@v~5
        (bvlshr badge___unsigned_longlong@v~4 (_ bv1 64)))
      node_upd_n14_ok)))
(assert
  (=
    node_upd_n14_ok
    (=>
      (=
        badge___unsigned_longlong@v@assigned~6
        badge___unsigned_longlong@v@assigned~5)
      node_guard_n13_ok)))
(assert
  (=
    node_guard_n13_ok
    (and
      (=> idx___unsigned@v@assigned~5 node_13_ok)
      (=> (not idx___unsigned@v@assigned~5) node_Err_ok_29))))
(assert
  (=
    node_13_ok
    (=>
      (= idx___unsigned@v~5 (bvadd idx___unsigned@v~4 (_ bv1 64)))
      node_upd_n13_ok)))
(assert
  (=
    node_upd_n13_ok
    (=> (= idx___unsigned@v@assigned~6 idx___unsigned@v@assigned~5) node_9_ok)))
(assert
  (=
    node_9_ok
    (=>
      (= loop@9@count~4 (bvadd loop@9@count~3 (_ bv1 64)))
      node_loop_10_latch_2_ok)))
(assert
  (=
    node_loop_10_latch_2_ok
    (=>
      (not
        (and
          (and
            (and (= HTD@assigned~8 true) (= Mem@assigned~8 true))
            (= PMS@assigned~8 true))
          (= GhostAssertions@assigned~8 true)))
      node_Err_ok_30)))
(assert
  (=
    node_8_ok
    (=> (= have_reply___char@v~3 ((_ extract 7 0) (_ bv1 64))) node_upd_n8_ok)))
(assert
  (=
    node_upd_n8_ok
    (=> (= have_reply___char@v@assigned~4 true) node_guard_n7_ok)))
(assert
  (=
    node_guard_n7_ok
    (and
      (=>
        (and
          (and
            (and
              (and
                (and Mem@assigned~3 badge___unsigned_longlong@v@assigned~3)
                GhostAssertions@assigned~3)
              PMS@assigned~3)
            tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
          HTD@assigned~3)
        node_prove_guard_n7_7_ok)
      (=>
        (not
          (and
            (and
              (and
                (and
                  (and Mem@assigned~3 badge___unsigned_longlong@v@assigned~3)
                  GhostAssertions@assigned~3)
                PMS@assigned~3)
              tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
            HTD@assigned~3))
        node_Err_ok_31))))
(assert (= node_prove_guard_n7_7_ok node_7_ok))
(assert (= node_7_ok node_assume_postcond_7_upd_n7_ok))
(assert (= node_assume_postcond_7_upd_n7_ok (=> true node_upd_n7_ok)))
(assert
  (=
    node_upd_n7_ok
    (=>
      (=
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4
        (and
          (and
            (and
              (and
                (and
                  badge___unsigned_longlong@v@assigned~3
                  tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                Mem@assigned~3)
              HTD@assigned~3)
            PMS@assigned~3)
          GhostAssertions@assigned~3))
      (=>
        (=
          Mem@assigned~4
          (and
            (and
              (and
                (and
                  (and
                    badge___unsigned_longlong@v@assigned~3
                    tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                  Mem@assigned~3)
                HTD@assigned~3)
              PMS@assigned~3)
            GhostAssertions@assigned~3))
        (=>
          (=
            HTD@assigned~4
            (and
              (and
                (and
                  (and
                    (and
                      badge___unsigned_longlong@v@assigned~3
                      tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                    Mem@assigned~3)
                  HTD@assigned~3)
                PMS@assigned~3)
              GhostAssertions@assigned~3))
          (=>
            (=
              PMS@assigned~4
              (and
                (and
                  (and
                    (and
                      (and
                        badge___unsigned_longlong@v@assigned~3
                        tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                      Mem@assigned~3)
                    HTD@assigned~3)
                  PMS@assigned~3)
                GhostAssertions@assigned~3))
            (=>
              (=
                GhostAssertions@assigned~4
                (and
                  (and
                    (and
                      (and
                        (and
                          badge___unsigned_longlong@v@assigned~3
                          tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                        Mem@assigned~3)
                      HTD@assigned~3)
                    PMS@assigned~3)
                  GhostAssertions@assigned~3))
              node_guard_n6_ok)))))))
(assert
  (=
    node_guard_n6_ok
    (and
      (=> rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 node_6_ok)
      (=>
        (not rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4)
        node_Err_ok_32))))
(assert
  (=
    node_6_ok
    (=>
      (=
        reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~2
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~3)
      node_upd_n6_ok)))
(assert
  (=
    node_upd_n6_ok
    (=>
      (=
        reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3
        rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4)
      node_j6_ok)))
(assert
  (=
    node_j6_ok
    (=>
      (= loop@9@count~4 loop@9@count~1)
      (=>
        (=
          reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~3
          reply_tag___struct_seL4_MessageInfo_C@v.words_C.0~2)
        (=>
          (= PMS~7 PMS~4)
          (=>
            (= Mem~7 Mem~4)
            (=>
              (=
                rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~4
                rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0~3)
              (=>
                (= badge___unsigned_longlong@v~5 badge___unsigned_longlong@v~2)
                (=>
                  (= HTD@assigned~7 HTD@assigned~4)
                  (=>
                    (=
                      rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~5
                      rv@space@ret__struct_seL4_MessageInfo_C@v.words_C.0@assigned~4)
                    (=>
                      (= GhostAssertions~7 GhostAssertions~4)
                      (=>
                        (= PMS@assigned~7 PMS@assigned~4)
                        (=>
                          (=
                            badge___unsigned_longlong@v@assigned~6
                            badge___unsigned_longlong@v@assigned~3)
                          (=>
                            (= GhostAssertions@assigned~7 GhostAssertions@assigned~4)
                            (=>
                              (= HTD~7 HTD~4)
                              (=>
                                (= idx___unsigned@v@assigned~6 idx___unsigned@v@assigned~2)
                                (=>
                                  (= idx___unsigned@v~5 idx___unsigned@v~1)
                                  (=>
                                    (=
                                      reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4
                                      reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~3)
                                    (=> (= Mem@assigned~7 Mem@assigned~4) node_2_ok)))))))))))))))))))
(assert
  (=
    node_2_ok
    (=>
      (= loop@2@count~3 (bvadd loop@2@count~2 (_ bv1 64)))
      node_loop_3_latch_2_ok)))
(assert
  (=
    node_loop_3_latch_2_ok
    (=>
      (not
        (and
          (and
            (and
              (and
                (and
                  (and
                    (=
                      (not (= is_endpoint___unsigned_longlong@v~2 (_ bv0 64)))
                      (not (= have_reply___char@v~3 (_ bv0 8))))
                    (=
                      (not (= is_endpoint___unsigned_longlong@v~2 (_ bv0 64)))
                      (= reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~4 true)))
                  (= HTD@assigned~7 true))
                (= Mem@assigned~7 true))
              (= PMS@assigned~7 true))
            (= GhostAssertions@assigned~7 true))
          (= have_reply___char@v@assigned~4 true)))
      node_Err_ok_33)))
(check-sat)
(assert (not node_49_ok))
(check-sat)
