(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema4.2b:
 Comparison of Area and Perimeter via realgeom, Bottema 4.2 (right triangle, ver. b):Let C, B be arbitrary points. Let a be the segment C, B. Let f be the line through C perpendicular to a. Let A be a point on f. Let c be the segment A, B. Let b be the segment C, A. Compare (a + b + c)^2 and a b / 2.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (> m 16))
(assert (< m 25))
(assert (and (< 0 m) (< 0 v11) (< 0 v9) (< 0 v10) (= (+ (* v8 v8) (* (* v9 v9) (- 1) )1) 0) (= (+ (* (* v11 v11) (- 1) )(* v8 v8)) 0) (= (+ (* v10 (- 1) )1) 0) (= (+ (* (* m v11) (- 1) )(* (* v11 v11) 2) (* (* v11 v9) 4) (* (* v9 v9) 2) (* v11 4) (* v9 4) 2) 0)))
(check-sat)
(exit)
