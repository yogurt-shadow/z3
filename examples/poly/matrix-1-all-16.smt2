(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "industrial")
(set-info :status sat)


(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)

(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))
(assert (>= x4 0))
(assert (>= x5 0))
(assert (>= x6 0))
(assert (>= x7 0))
(assert (>= x8 0))
(assert (>= x9 0))

(assert (let ((?v_0 (+ (+ 0 (* 0 x7)) (* 1 x7))) (?v_1 (+ 1 (* x1 x7))) (?v_3 (+ x7 (* 6 x7)))) (let ((?v_2 (+ 1 (* 1 ?v_3))) (?v_5 (* 6 6)) (?v_4 (+ 1 (* 1 ?v_3))) (?v_26 (+ x7 (* 6 x8)))) (let ((?v_6 (+ x5 (* x0 ?v_26))) (?v_8 (+ 1 (* 1 x7))) (?v_7 (+ x5 (* 2 x7))) (?v_10 (* 2 6))) (let ((?v_11 (and (> ?v_7 1) (>= ?v_7 1))) (?v_14 (+ 1 (* x2 x7)))) (let ((?v_9 (+ (+ x5 (* x9 1)) (* 2 ?v_14))) (?v_16 (+ 0 0)) (?v_17 (* x2 6)) (?v_12 (+ x5 (* x0 1))) (?v_13 (+ 1 (* 1 x7))) (?v_35 (+ 1 (* x4 x7))) (?v_36 (+ 1 (* 1 1))) (?v_37 (+ (+ 1 (* 1 1)) (* 1 ?v_14)))) (let ((?v_15 (+ (+ (+ 1 (* 1 ?v_35)) (* 1 ?v_36)) (* 0 ?v_37))) (?v_40 (+ 1 (* 1 0))) (?v_41 (* 1 ?v_16)) (?v_42 (* x4 6)) (?v_43 (* 1 ?v_17)) (?v_44 (* 1 0))) (let ((?v_45 (and (and (and (and (and (and (and (and (and (and (and (and (and (and (> ?v_0 0) (>= ?v_0 0)) (>= (* 0 6) 0)) (>= (* 1 6) 1)) (and (and (> ?v_1 1) (>= ?v_1 1)) (>= (* x1 6) x1))) (and (and (> ?v_2 1) (>= ?v_2 1)) (>= (* 1 ?v_5) 1))) (and (and (> ?v_4 1) (>= ?v_4 1)) (>= (* 1 ?v_5) 1))) (and (and (and (> 1 ?v_6) (>= 1 ?v_6)) (>= 2 x9)) (>= 3 2))) (and (and (> ?v_7 ?v_8) (>= ?v_7 ?v_8)) (>= ?v_10 (* 1 6)))) (and ?v_11 (>= x9 (+ 1 x1)))) (and (and (and (> ?v_7 ?v_9) (>= ?v_7 ?v_9)) (>= x9 (* x9 ?v_16))) (>= ?v_10 (* 2 ?v_17)))) (and (and ?v_11 (>= x9 1)) (>= x0 x1))) (and (and (and (and (> ?v_7 ?v_12) (>= ?v_7 ?v_12)) (>= x9 (+ x9 (* x0 0)))) (>= ?v_10 2)) (>= x0 (* x0 0)))) (and (and (> ?v_7 ?v_13) (>= ?v_7 ?v_13)) (>= ?v_10 (* 1 6)))) (and (and (and (and (> ?v_7 ?v_15) (>= ?v_7 ?v_15)) (>= x9 (+ (* 1 ?v_40) (* 0 ?v_41)))) (>= ?v_10 (+ (+ (* 1 ?v_42) (* 1 1)) (* 0 ?v_43)))) (>= x0 (+ (* 1 ?v_44) (* 0 1)))))) (?v_18 (+ 1 (* 1 x8))) (?v_19 (+ (+ 1 (* 1 x7)) (* 1 x7))) (?v_20 (+ 1 (* 0 x8))) (?v_22 (+ x3 (* x6 1))) (?v_21 (+ 1 (* 0 x7))) (?v_23 (+ 1 (* 1 1))) (?v_24 (+ 1 (* 1 1))) (?v_25 (+ 1 (* x4 x8))) (?v_27 (+ 1 (* x4 ?v_26))) (?v_28 (+ 1 (* x4 ?v_3))) (?v_29 (+ 1 (* x2 x8))) (?v_30 (+ 1 (* x2 ?v_26))) (?v_32 (+ x7 (* 6 1))) (?v_31 (+ 1 (* x2 ?v_3))) (?v_33 (+ 1 (* 1 ?v_26))) (?v_34 (+ 1 (* 1 x8))) (?v_39 (+ (+ (+ 1 (* 1 ?v_35)) (* 1 ?v_36)) (* 1 ?v_37))) (?v_38 (+ 1 (* 1 x7)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and ?v_45 (and (and (> ?v_18 0) (>= ?v_18 0)) (>= 1 1))) (and (and (and (> ?v_19 1) (>= ?v_19 1)) (>= (* 1 6) 1)) (>= (* 1 6) 1))) (and (> ?v_20 x8) (>= ?v_20 x8))) (and (and (and (> ?v_21 ?v_22) (>= ?v_21 ?v_22)) (>= 0 (+ (* x6 0) 0))) (>= (* 0 6) (* x6 0)))) (and (and (> ?v_23 0) (>= ?v_23 0)) (>= 1 1))) (and (and (> ?v_24 0) (>= ?v_24 0)) (>= 1 1))) (and (> ?v_25 1) (>= ?v_25 1))) (and (> ?v_27 1) (>= ?v_27 1))) (and (and (> ?v_28 1) (>= ?v_28 1)) (>= (* x4 ?v_5) x4))) (and (> ?v_29 x8) (>= ?v_29 x8))) (and (> ?v_30 x8) (>= ?v_30 x8))) (and (and (> ?v_31 ?v_32) (>= ?v_31 ?v_32)) (>= (* x2 ?v_5) (* 6 x2)))) (and (> ?v_23 1) (>= ?v_23 1))) (and (> ?v_24 1) (>= ?v_24 1))) (and (and (and (> 9 ?v_33) (>= 9 ?v_33)) (>= 1 1)) (>= 2 1))) (and (and (> ?v_34 0) (>= ?v_34 0)) (>= 1 1))) (and (and (and (and (> ?v_38 ?v_39) (>= ?v_38 ?v_39)) (>= 1 (+ (* 1 ?v_40) (* 1 ?v_41)))) (>= (* 1 6) (+ (+ (* 1 ?v_42) (* 1 1)) (* 1 ?v_43)))) (>= 1 (+ (* 1 ?v_44) (* 1 1))))) ?v_45)))))))))
(check-sat)
(get-model)
(exit)
