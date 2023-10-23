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
(assert (let ((?v_2 (<= 0 skoY)) (?v_0 (* skoX (/ (- 399) 50))) (?v_1 (* skoX (/ 399 100))) (?v_3 (* skoX (- 1)))) (and (<= 0 skoX) (and ?v_2 (and (<= (* skoZ (+ (+ (+ 9 (* skoX (+ (/ 1197 50) (* skoX (+ 21 (* skoX (/ 399 50))))))) (* skoY (+ (+ (/ 1197 50) (* skoX (+ 18 (* skoX (+ (/ (- 399) 25) (* skoX (+ (- 18) ?v_0))))))) (* skoY (+ (+ 18 (* skoX (+ (/ (- 1197) 50) (* skoX (+ (- 21) (* skoX (+ (/ (- 399) 50) (* skoX (- 3))))))))) (* skoY (* skoX (+ (- 18) (* skoX (* skoX (- 6))))))))))) (* skoZ (+ (+ (/ 1197 100) (* skoX (+ 9 ?v_1))) (* skoY (+ (+ 9 (* skoX (+ (/ (- 1197) 50) (* skoX (+ (- 15) ?v_0))))) (* skoY (+ (* skoX (+ (- 18) (* skoX (+ (/ 1197 100) (* skoX (+ 3 ?v_1)))))) (* skoY (* skoX (* skoX (+ 9 (* skoX (* skoX 3)))))))))))))) (+ (+ (/ (- 399) 100) (* skoX (+ (- 12) (* skoX (+ (/ (- 133) 10) (* skoX (+ (- 12) (* skoX (/ (- 399) 100))))))))) (* skoY (+ (+ (- 12) (* skoX (+ (/ (- 399) 25) (* skoX (+ (- 16) (* skoX (/ (- 133) 25))))))) (* skoY (+ (+ (/ (- 1197) 100) (* skoX (+ (- 12) (* skoX (+ (/ (- 399) 50) (* skoX (+ (- 4) (* skoX (/ (- 133) 100))))))))) (* skoY (+ (- 9) (* skoX (* skoX (+ (- 6) (* skoX ?v_3)))))))))))) (and (or ?v_2 (<= (* skoZ (+ 1 (* skoY ?v_3))) (+ (+ 1 ?v_3) (* skoY (+ (- 1) ?v_3))))) (and (or (not ?v_2) (<= (* skoZ (+ (- 1) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX))))))))))))
(check-sat)
(exit)
