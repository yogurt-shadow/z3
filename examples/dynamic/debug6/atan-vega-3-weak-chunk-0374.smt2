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
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_3 (* skoX 3)) (?v_5 (<= 0 skoY)) (?v_0 (* skoX (- 6)))) (let ((?v_1 (* skoX (+ (/ (- 399) 50) ?v_0))) (?v_2 (+ (/ 399 100) ?v_3)) (?v_4 (* skoX (- 1)))) (and (<= 0 skoX) (and (<= (* skoZ (+ (+ (+ 3 (* skoX (+ (/ 399 50) (* skoX 6)))) (* skoY (+ (+ (/ 399 50) (* skoX (+ 6 ?v_1))) (* skoY (+ (+ 6 (* skoX (+ (/ (- 399) 50) (* skoX (- 9))))) (* skoY ?v_0)))))) (* skoZ (+ ?v_2 (* skoY (+ (+ 3 ?v_1) (* skoY (+ (* skoX (+ (- 6) (* skoX ?v_2))) (* skoY (* skoX ?v_3)))))))))) (+ (+ (/ (- 133) 100) (* skoX (+ (- 4) (* skoX (+ (/ (- 399) 100) (* skoX (- 3))))))) (* skoY (+ (+ (- 4) (* skoX (+ (/ (- 133) 25) (* skoX (- 4))))) (* skoY (+ (+ (/ (- 399) 100) (* skoX (+ (- 4) (* skoX (+ (/ (- 133) 100) ?v_4))))) (* skoY (+ (- 3) (* skoX ?v_4))))))))) (and (or ?v_5 (<= (* skoZ (+ 1 (* skoY ?v_4))) (+ (+ 1 ?v_4) (* skoY (+ (- 1) ?v_4))))) (and (or (not ?v_5) (<= (* skoZ (+ (- 1) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX))))))))))))
(check-sat)
(exit)
