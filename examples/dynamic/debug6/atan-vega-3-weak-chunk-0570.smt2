(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_2 (* skoX 12)) (?v_0 (* skoX (/ (- 3) 2))) (?v_1 (* skoX (/ 3 4))) (?v_3 (* skoX (/ (- 3) 4)))) (and (not (<= 0 skoY)) (and (not (<= (* skoX (* skoX (- 1))) 3)) (and (not (<= (* skoZ (+ (+ (+ 27 (* skoX (+ (/ 9 2) (* skoX (+ (- 9) (* skoX (/ 3 2))))))) (* skoY (+ (+ (/ 9 2) (* skoX (+ (- 90) (* skoX (+ (- 3) (* skoX (+ (- 6) ?v_0))))))) (* skoY (+ (+ (- 9) (* skoX (+ (- 3) (* skoX (+ 54 (* skoX (+ (- 1) (* skoX 15)))))))) (* skoY (+ (+ (/ 3 2) (* skoX (+ (- 6) (* skoX (+ (- 1) (* skoX (+ 6 (* skoX (/ (- 1) 2))))))))) (* skoY (* skoX (+ (/ (- 3) 2) (* skoX (+ 15 (* skoX (+ (/ (- 1) 2) (* skoX 3))))))))))))))) (* skoZ (+ (+ (/ 9 4) (* skoX (+ (- 9) ?v_1))) (* skoY (+ (+ (- 9) (* skoX (+ (/ (- 9) 2) (* skoX (+ 15 ?v_0))))) (* skoY (+ (+ (/ 3 4) (* skoX (+ 15 (* skoX (+ (/ 5 2) (* skoX (+ (- 3) ?v_1))))))) (* skoY (+ (* skoX (+ (/ (- 3) 2) (* skoX (+ (- 3) (* skoX (+ (/ (- 1) 2) (* skoX (- 3)))))))) (* skoY (* skoX (* skoX (+ (/ 3 4) (* skoX (+ (- 3) (* skoX (/ 1 4)))))))))))))))))) (+ (+ (/ (- 27) 4) (* skoX (* skoX (+ (/ (- 9) 2) (* skoX ?v_3))))) (* skoY (+ (* skoX (+ 9 (* skoX (* skoX (+ 3 ?v_2))))) (* skoY (+ (+ (/ (- 9) 2) (* skoX (* skoX (+ (- 9) (* skoX (+ 24 (* skoX (/ (- 5) 2)))))))) (* skoY (+ (* skoX (+ 3 (* skoX (+ 24 (* skoX (+ 1 ?v_2)))))) (* skoY (+ (/ (- 3) 4) (* skoX (+ 12 (* skoX (+ (/ (- 5) 2) (* skoX (+ 12 ?v_3))))))))))))))))) (and (not (<= 0 skoX)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX)))))))))))
(check-sat)
(exit)
