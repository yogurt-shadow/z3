(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoRightTriangle-Bottema1.1a:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 1.1 (isosceles right triangle, ver. a):Let C, A be arbitrary points. Let a be the segment C, A. Let d be the circle through A with center C. Let f be the line through C perpendicular to a. Let B be the intersection point of d, f. Let c be the segment B, A. Compare (2a + c)^2 and a^2 + 2a c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v9) (< 0 v10) (= (+ (* (* v8 v8) (- 1) )1) 0) (= (+ (* v8 v8) (* (* v9 v9) (- 1) )1) 0) (= (+ (* v10 (- 1) )1) 0) (= (+ (* (* m v9) (- 2) )(* v9 v9) (* m (- 1) )(* v9 4) 4) 0)))
(check-sat)
(exit)
