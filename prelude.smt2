(set-logic QF_ABV)
; data Ch = Ch0 | Ch1 | .. | Ch62
;  <elements> = 7
;  <bit size> = 3
(define-sort Ch () (_ BitVec 8))
(declare-fun Ch_constructor_Ch0 () Ch)
(declare-fun Ch_constructor_Ch1 () Ch)
(declare-fun Ch_constructor_Ch2 () Ch)
(declare-fun Ch_constructor_Ch3 () Ch)
(declare-fun Ch_constructor_Ch4 () Ch)
(declare-fun Ch_constructor_Ch5 () Ch)
(declare-fun Ch_constructor_Ch6 () Ch)
(declare-fun Ch_constructor_Ch7 () Ch)
(declare-fun Ch_constructor_Ch8 () Ch)
(declare-fun Ch_constructor_Ch9 () Ch)
(declare-fun Ch_constructor_Ch10 () Ch)
(declare-fun Ch_constructor_Ch11 () Ch)
(declare-fun Ch_constructor_Ch12 () Ch)
(declare-fun Ch_constructor_Ch13 () Ch)
(declare-fun Ch_constructor_Ch14 () Ch)
(declare-fun Ch_constructor_Ch15 () Ch)
(declare-fun Ch_constructor_Ch16 () Ch)
(declare-fun Ch_constructor_Ch17 () Ch)
(declare-fun Ch_constructor_Ch18 () Ch)
(declare-fun Ch_constructor_Ch19 () Ch)
(declare-fun Ch_constructor_Ch20 () Ch)
(declare-fun Ch_constructor_Ch21 () Ch)
(declare-fun Ch_constructor_Ch22 () Ch)
(declare-fun Ch_constructor_Ch23 () Ch)
(declare-fun Ch_constructor_Ch24 () Ch)
(declare-fun Ch_constructor_Ch25 () Ch)
(declare-fun Ch_constructor_Ch26 () Ch)
(declare-fun Ch_constructor_Ch27 () Ch)
(declare-fun Ch_constructor_Ch28 () Ch)
(declare-fun Ch_constructor_Ch29 () Ch)
(declare-fun Ch_constructor_Ch30 () Ch)
(declare-fun Ch_constructor_Ch31 () Ch)
(declare-fun Ch_constructor_Ch32 () Ch)
(declare-fun Ch_constructor_Ch33 () Ch)
(declare-fun Ch_constructor_Ch34 () Ch)
(declare-fun Ch_constructor_Ch35 () Ch)
(declare-fun Ch_constructor_Ch36 () Ch)
(declare-fun Ch_constructor_Ch37 () Ch)
(declare-fun Ch_constructor_Ch38 () Ch)
(declare-fun Ch_constructor_Ch39 () Ch)
(declare-fun Ch_constructor_Ch40 () Ch)
(declare-fun Ch_constructor_Ch41 () Ch)
(declare-fun Ch_constructor_Ch42 () Ch)
(declare-fun Ch_constructor_Ch43 () Ch)
(declare-fun Ch_constructor_Ch44 () Ch)
(declare-fun Ch_constructor_Ch45 () Ch)
(declare-fun Ch_constructor_Ch46 () Ch)
(declare-fun Ch_constructor_Ch47 () Ch)
(declare-fun Ch_constructor_Ch48 () Ch)
(declare-fun Ch_constructor_Ch49 () Ch)
(declare-fun Ch_constructor_Ch50 () Ch)
(declare-fun Ch_constructor_Ch51 () Ch)
(declare-fun Ch_constructor_Ch52 () Ch)
(declare-fun Ch_constructor_Ch53 () Ch)
(declare-fun Ch_constructor_Ch54 () Ch)
(declare-fun Ch_constructor_Ch55 () Ch)
(declare-fun Ch_constructor_Ch56 () Ch)
(declare-fun Ch_constructor_Ch57 () Ch)
(declare-fun Ch_constructor_Ch58 () Ch)
(declare-fun Ch_constructor_Ch59 () Ch)
(declare-fun Ch_constructor_Ch60 () Ch)
(declare-fun Ch_constructor_Ch61 () Ch)
(declare-fun Ch_constructor_Ch62 () Ch)

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

(define-fun lc_unhandled_ppcall () Maybe_Prod_Ch_MsgInfo Maybe_Prod_Ch_MsgInfo_Nothing)

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

(define-fun construct-prod-just ((mi_label (_ BitVec 64)) (ch Ch)) (Maybe_Prod_Ch_MsgInfo) 
  (Maybe_Prod_Ch_MsgInfo_Just (construct-prod mi_label ch))
)





