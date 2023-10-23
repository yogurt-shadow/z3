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
(set-info :status sat)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_4 (not (<= 0 skoY))) (?v_2 (* skoX (- 3)))) (let ((?v_0 (* skoX ?v_2)) (?v_3 (* skoX (- 1)))) (let ((?v_6 (* skoX ?v_3))) (let ((?v_7 (* skoY (* skoX (+ (- 3) ?v_6))))) (let ((?v_5 (+ (+ 3 (* skoX skoX)) ?v_7)) (?v_1 (* skoX (* skoX (- 4))))) (and (<= (* skoZ (+ (+ 9 (* skoX (* skoX 3))) (* skoY (+ (* skoX (+ (- 9) ?v_0)) (* skoY ?v_5))))) (+ (* skoX ?v_0) (* skoY (+ (* skoX (* skoX (- 9))) (* skoY (+ (* skoX (+ (- 9) ?v_1)) (* skoY (+ (- 3) ?v_1)))))))) (and ?v_4 (and (not (<= (* skoY (+ ?v_2 (* skoY (+ 1 (* skoY ?v_3))))) (- 3))) (and (or ?v_4 (or (<= (* skoZ (+ (- 1) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ ?v_5) (+ (* skoX ?v_6) (* skoY (+ ?v_0 ?v_7)))))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX)))))))))))))))
(check-sat)
(exit)
