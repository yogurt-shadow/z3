(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RegHeptagon-Diagonal_Side:
 Comparison of Diagonal and Side (regular heptagon):Let A, B be arbitrary points. Let poly1 be the regular 7-gon with vertices A, B, C, D, E, F, G. Let f be the segment A, B. Let m be the segment G, C. Compare segment G, C and segment A, B.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v18) (< 0 v19) (= (+ (* v7 v7) (* (* v8 v8) (- 1) )(* v7 (- 1) )(* v9 (- 1) )1) 0) (= (- (* (* v7 v8) 2) v10 v8) 0) (= (+ (* (* v10 v8) (- 1) )(* (* v7 v7) (- 1) )(* v7 v9) (* v8 v8) (* v11 (- 1) )v7) 0) (= (+ (* v10 v7) (* (* v7 v8) (- 2) )(* v8 v9) (* v12 (- 1) )v8) 0) (= (+ (* v10 v8) (* v11 v7) (* (* v8 v12) (- 1) )(* (* v7 v9) (- 1) )(* v13 (- 1) )v9) 0) (= (+ (* (* v10 v7) (- 1) )(* v11 v8) (* v12 v7) (* (* v8 v9) (- 1) )v10 (* v14 (- 1))) 0) (= (+ (* (* v11 v7) (- 1) )(* v8 v12) (* v13 v7) (* (* v8 v14) (- 1) )v11 (* v15 (- 1))) 0) (= (+ (* (* v11 v8) (- 1) )(* (* v12 v7) (- 1) )(* v8 v13) (* v14 v7) v12 (* v16 (- 1))) 0) (= (+ (* v15 v15) (* (* v7 v15) (- 2) )(* v16 v16) (* (* v8 v16) (- 2) )(* (* v18 v18) (- 1) )(* v7 v7) (* v8 v8)) 0) (= (+ (* v7 v7) (* v8 v8) (* v7 (- 2))) 0) (= (+ (* (* v7 v7 v7) 8) (* (* v7 v7) (- 20) )(* v7 12) (- 1) )0) (= (+ (* m (- 1) )v18) 0) (= (+ (* v19 (- 1) )1) 0)))
(check-sat)
(exit)
