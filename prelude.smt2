(set-logic QF_ABV)
; data Ch = Ch0 | Ch1 | .. | Ch62
;  <elements> = 7
;  <bit size> = 3
(define-sort Ch () (_ BitVec 8))
(define-fun Ch_constructor_Ch0 () Ch (_ bv0 8))
(define-fun Ch_constructor_Ch1 () Ch (_ bv1 8))
(define-fun Ch_constructor_Ch2 () Ch (_ bv2 8))
(define-fun Ch_constructor_Ch3 () Ch (_ bv3 8))
(define-fun Ch_constructor_Ch4 () Ch (_ bv4 8))
(define-fun Ch_constructor_Ch5 () Ch (_ bv5 8))
(define-fun Ch_constructor_Ch6 () Ch (_ bv6 8))
(define-fun Ch_constructor_Ch7 () Ch (_ bv7 8))
(define-fun Ch_constructor_Ch8 () Ch (_ bv8 8))
(define-fun Ch_constructor_Ch9 () Ch (_ bv9 8))
(define-fun Ch_constructor_Ch10 () Ch (_ bv10 8))
(define-fun Ch_constructor_Ch11 () Ch (_ bv11 8))
(define-fun Ch_constructor_Ch12 () Ch (_ bv12 8))
(define-fun Ch_constructor_Ch13 () Ch (_ bv13 8))
(define-fun Ch_constructor_Ch14 () Ch (_ bv14 8))
(define-fun Ch_constructor_Ch15 () Ch (_ bv15 8))
(define-fun Ch_constructor_Ch16 () Ch (_ bv16 8))
(define-fun Ch_constructor_Ch17 () Ch (_ bv17 8))
(define-fun Ch_constructor_Ch18 () Ch (_ bv18 8))
(define-fun Ch_constructor_Ch19 () Ch (_ bv19 8))
(define-fun Ch_constructor_Ch20 () Ch (_ bv20 8))
(define-fun Ch_constructor_Ch21 () Ch (_ bv21 8))
(define-fun Ch_constructor_Ch22 () Ch (_ bv22 8))
(define-fun Ch_constructor_Ch23 () Ch (_ bv23 8))
(define-fun Ch_constructor_Ch24 () Ch (_ bv24 8))
(define-fun Ch_constructor_Ch25 () Ch (_ bv25 8))
(define-fun Ch_constructor_Ch26 () Ch (_ bv26 8))
(define-fun Ch_constructor_Ch27 () Ch (_ bv27 8))
(define-fun Ch_constructor_Ch28 () Ch (_ bv28 8))
(define-fun Ch_constructor_Ch29 () Ch (_ bv29 8))
(define-fun Ch_constructor_Ch30 () Ch (_ bv30 8))
(define-fun Ch_constructor_Ch31 () Ch (_ bv31 8))
(define-fun Ch_constructor_Ch32 () Ch (_ bv32 8))
(define-fun Ch_constructor_Ch33 () Ch (_ bv33 8))
(define-fun Ch_constructor_Ch34 () Ch (_ bv34 8))
(define-fun Ch_constructor_Ch35 () Ch (_ bv35 8))
(define-fun Ch_constructor_Ch36 () Ch (_ bv36 8))
(define-fun Ch_constructor_Ch37 () Ch (_ bv37 8))
(define-fun Ch_constructor_Ch38 () Ch (_ bv38 8))
(define-fun Ch_constructor_Ch39 () Ch (_ bv39 8))
(define-fun Ch_constructor_Ch40 () Ch (_ bv40 8))
(define-fun Ch_constructor_Ch41 () Ch (_ bv41 8))
(define-fun Ch_constructor_Ch42 () Ch (_ bv42 8))
(define-fun Ch_constructor_Ch43 () Ch (_ bv43 8))
(define-fun Ch_constructor_Ch44 () Ch (_ bv44 8))
(define-fun Ch_constructor_Ch45 () Ch (_ bv45 8))
(define-fun Ch_constructor_Ch46 () Ch (_ bv46 8))
(define-fun Ch_constructor_Ch47 () Ch (_ bv47 8))
(define-fun Ch_constructor_Ch48 () Ch (_ bv48 8))
(define-fun Ch_constructor_Ch49 () Ch (_ bv49 8))
(define-fun Ch_constructor_Ch50 () Ch (_ bv50 8))
(define-fun Ch_constructor_Ch51 () Ch (_ bv51 8))
(define-fun Ch_constructor_Ch52 () Ch (_ bv52 8))
(define-fun Ch_constructor_Ch53 () Ch (_ bv53 8))
(define-fun Ch_constructor_Ch54 () Ch (_ bv54 8))
(define-fun Ch_constructor_Ch55 () Ch (_ bv55 8))
(define-fun Ch_constructor_Ch56 () Ch (_ bv56 8))
(define-fun Ch_constructor_Ch57 () Ch (_ bv57 8))
(define-fun Ch_constructor_Ch58 () Ch (_ bv58 8))
(define-fun Ch_constructor_Ch59 () Ch (_ bv59 8))
(define-fun Ch_constructor_Ch60 () Ch (_ bv60 8))
(define-fun Ch_constructor_Ch61 () Ch (_ bv61 8))
(define-fun Ch_constructor_Ch62 () Ch (_ bv62 8))
(assert (distinct Ch_constructor_Ch0 Ch_constructor_Ch1 Ch_constructor_Ch2 Ch_constructor_Ch3 Ch_constructor_Ch4 Ch_constructor_Ch5 Ch_constructor_Ch6 Ch_constructor_Ch7 Ch_constructor_Ch8 Ch_constructor_Ch9 Ch_constructor_Ch10 Ch_constructor_Ch11 Ch_constructor_Ch12 Ch_constructor_Ch13 Ch_constructor_Ch14 Ch_constructor_Ch15 Ch_constructor_Ch16 Ch_constructor_Ch17 Ch_constructor_Ch18 Ch_constructor_Ch19 Ch_constructor_Ch20 Ch_constructor_Ch21 Ch_constructor_Ch22 Ch_constructor_Ch23 Ch_constructor_Ch24 Ch_constructor_Ch25 Ch_constructor_Ch26 Ch_constructor_Ch27 Ch_constructor_Ch28 Ch_constructor_Ch29 Ch_constructor_Ch30 Ch_constructor_Ch31 Ch_constructor_Ch32 Ch_constructor_Ch33 Ch_constructor_Ch34 Ch_constructor_Ch35 Ch_constructor_Ch36 Ch_constructor_Ch37 Ch_constructor_Ch38 Ch_constructor_Ch39 Ch_constructor_Ch40 Ch_constructor_Ch41 Ch_constructor_Ch42 Ch_constructor_Ch43 Ch_constructor_Ch44 Ch_constructor_Ch45 Ch_constructor_Ch46 Ch_constructor_Ch47 Ch_constructor_Ch48 Ch_constructor_Ch49 Ch_constructor_Ch50 Ch_constructor_Ch51 Ch_constructor_Ch52 Ch_constructor_Ch53 Ch_constructor_Ch54 Ch_constructor_Ch55 Ch_constructor_Ch56 Ch_constructor_Ch57 Ch_constructor_Ch58 Ch_constructor_Ch59 Ch_constructor_Ch60 Ch_constructor_Ch61 Ch_constructor_Ch62))
(assert (distinct Ch_constructor_Ch0 Ch_constructor_Ch1 Ch_constructor_Ch2 Ch_constructor_Ch3 Ch_constructor_Ch4 Ch_constructor_Ch5 Ch_constructor_Ch6 Ch_constructor_Ch7 Ch_constructor_Ch8 Ch_constructor_Ch9 Ch_constructor_Ch10 Ch_constructor_Ch11 Ch_constructor_Ch12 Ch_constructor_Ch13 Ch_constructor_Ch14 Ch_constructor_Ch15 Ch_constructor_Ch16 Ch_constructor_Ch17 Ch_constructor_Ch18 Ch_constructor_Ch19 Ch_constructor_Ch20 Ch_constructor_Ch21 Ch_constructor_Ch22 Ch_constructor_Ch23 Ch_constructor_Ch24 Ch_constructor_Ch25 Ch_constructor_Ch26 Ch_constructor_Ch27 Ch_constructor_Ch28 Ch_constructor_Ch29 Ch_constructor_Ch30 Ch_constructor_Ch31 Ch_constructor_Ch32 Ch_constructor_Ch33 Ch_constructor_Ch34 Ch_constructor_Ch35 Ch_constructor_Ch36 Ch_constructor_Ch37 Ch_constructor_Ch38 Ch_constructor_Ch39 Ch_constructor_Ch40 Ch_constructor_Ch41 Ch_constructor_Ch42 Ch_constructor_Ch43 Ch_constructor_Ch44 Ch_constructor_Ch45 Ch_constructor_Ch46 Ch_constructor_Ch47 Ch_constructor_Ch48 Ch_constructor_Ch49 Ch_constructor_Ch50 Ch_constructor_Ch51 Ch_constructor_Ch52 Ch_constructor_Ch53 Ch_constructor_Ch54 Ch_constructor_Ch55 Ch_constructor_Ch56 Ch_constructor_Ch57 Ch_constructor_Ch58 Ch_constructor_Ch59 Ch_constructor_Ch60 Ch_constructor_Ch61 Ch_constructor_Ch62))

; data MsgInfo = MI { mi_label :: Word64 , mi_count :: Word16 }
(define-sort MsgInfo () (_ BitVec 80))
(define-fun mi_label ((mi MsgInfo)) (_ BitVec 64) ((_ extract 79 16) mi))
(define-fun mi_count ((mi MsgInfo)) (_ BitVec 16) ((_ extract 15 0) mi))

(define-fun set_mi_label ((mi MsgInfo) (label (_ BitVec 64))) MsgInfo (concat label (mi_count mi)))
(define-fun set_mi_count ((mi MsgInfo) (count (_ BitVec 16))) MsgInfo (concat (mi_label mi) count))

; newtype Prod_Ch_MsgInfo = (Ch, MsgInfo)
(define-sort Prod_Ch_MsgInfo () (_ BitVec 88))
(define-fun Prod_Ch_MsgInfo_fst ((p Prod_Ch_MsgInfo)) Ch ((_ extract 87 80) p))
(define-fun Prod_Ch_MsgInfo_snd ((p Prod_Ch_MsgInfo)) MsgInfo ((_ extract 79 0) p))

(define-fun set_Prod_Ch_MsgInfo_fst ((p Prod_Ch_MsgInfo) (ch Ch)) Prod_Ch_MsgInfo (concat ch (Prod_Ch_MsgInfo_snd p)))
(define-fun set_Prod_Ch_MsgInfo_snd ((p Prod_Ch_MsgInfo) (mi MsgInfo)) Prod_Ch_MsgInfo (concat (Prod_Ch_MsgInfo_fst p) mi))


; data Maybe A = Just A | Nothing
; Maybe_Prod_Ch_MsgInfo = Maybe (Ch, MsgInfo)
; effectively (Just | Nothing, (Ch, MsgInfo))

(define-sort Maybe_Prod_Ch_MsgInfo () (_ BitVec 89))
(define-sort Maybe_Prod_Ch_MsgInfo_constructor () (_ BitVec 1))

(declare-fun Maybe_Prod_Ch_MsgInfo_constructor_Nothing () Maybe_Prod_Ch_MsgInfo_constructor)
(declare-fun Maybe_Prod_Ch_MsgInfo_constructor_Just () Maybe_Prod_Ch_MsgInfo_constructor)

(assert (distinct Maybe_Prod_Ch_MsgInfo_constructor_Nothing Maybe_Prod_Ch_MsgInfo_constructor_Just))

; function to access the constructor
(define-fun Maybe_Prod_Ch_MsgInfo_constructor ((m Maybe_Prod_Ch_MsgInfo)) Maybe_Prod_Ch_MsgInfo_constructor ((_ extract 88 88) m))
(define-fun Maybe_Prod_Ch_MsgInfo_Just_arg1 ((m Maybe_Prod_Ch_MsgInfo)) Prod_Ch_MsgInfo ((_ extract 87 0) m))

; (define-fun set_Maybe_Prod_Ch_MsgInfo_constructor ((m Maybe_Prod_Ch_MsgInfo) (c Maybe_Prod_Ch_MsgInfo_constructor)) Maybe_Prod_Ch_MsgInfo (concat c ((_ extract 87 0) m)))
(define-fun Maybe_Prod_Ch_MsgInfo_Just ((p Prod_Ch_MsgInfo)) Maybe_Prod_Ch_MsgInfo (concat Maybe_Prod_Ch_MsgInfo_constructor_Just p))
(define-fun Maybe_Prod_Ch_MsgInfo_Nothing () Maybe_Prod_Ch_MsgInfo (concat Maybe_Prod_Ch_MsgInfo_constructor_Nothing (_ bv0 88)))

(define-fun construct-prod ((mi_label (_ BitVec 64)) (ch Ch)) (Prod_Ch_MsgInfo) 
  (set_Prod_Ch_MsgInfo_fst 
    (set_Prod_Ch_MsgInfo_snd 
      (_ bv0 88) 
      (set_mi_label 
        (_ bv0 80) mi_label 
      )
    )
    ch 
  ) 
)

(define-fun construct-prod-just ((ch64 (_ BitVec 64)) (mi_label (_ BitVec 64))) (Maybe_Prod_Ch_MsgInfo) 
  (Maybe_Prod_Ch_MsgInfo_Just (construct-prod mi_label (_ bv0 8)))
)

(define-sort PD () (_ BitVec 3))
(define-sort Word64 () (_ BitVec 64))
(define-sort Word16 () (_ BitVec 16))

(define-sort Ch_set () (_ BitVec 256))
(define-fun Ch_set_empty () Ch_set (_ bv0 256))
(define-fun Ch_set_singleton ((x Ch)) Ch_set (bvshl (_ bv1 256) ((_ zero_extend 248) x)))
(define-fun Ch_set_intersection ((s1 Ch_set) (s2 Ch_set)) Ch_set (bvand s1 s2))
(define-fun Ch_set_union ((s1 Ch_set) (s2 Ch_set)) Ch_set (bvor s1 s2))
(define-fun Ch_set_has ((s Ch_set) (x Ch)) Bool (bvult (_ bv0 256) (bvand s (Ch_set_singleton x))))
(define-fun Ch_set_add ((s Ch_set) (x Ch)) Ch_set (Ch_set_union s (Ch_set_singleton x)))
(define-fun Ch_set_remove ((s Ch_set) (x Ch)) Ch_set (Ch_set_intersection s (Ch_set_singleton x)))

(define-fun lc_unhandled_ppcall~1 () Maybe_Prod_Ch_MsgInfo Maybe_Prod_Ch_MsgInfo_Nothing)