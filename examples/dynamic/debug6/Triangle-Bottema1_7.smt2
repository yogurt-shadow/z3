(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

Triangle-Bottema1.7:
 Comparison of Expressions Related to Triangle Sides via realgeom (Bottema 1.7):Let A, B, C be arbitrary points. Let t1 be the polygon A, B, C. Let c be the segment A, B. Let a be the segment B, C. Let b be the segment C, A. Compare 1 / 2 (a^2 (b + c - a) + b^2 (a + c - b) + c^2 (a + b - c)) and a b c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v8) (< 0 v7) (< 0 v9) (= (+ (* v5 v5) (* v6 v6) (* (* v7 v7) (- 1) )(* v5 (- 2) )1) 0) (= (+ (* v5 v5) (* v6 v6) (* (* v8 v8) (- 1))) 0) (= (+ (* v10 v6) (- 1) )0) (= (+ (* v9 (- 1) )1) 0) (= (+ (* (* m v7 v8) (- 2) )(* (* v7 v7 v7) (- 1) )(* (* v7 v7) v8) (* v7 (* v8 v8)) (* (* v8 v8 v8) (- 1) )(* v7 v7) (* v8 v8) v7 v8 (- 1) )0)))
(check-sat)
(exit)
