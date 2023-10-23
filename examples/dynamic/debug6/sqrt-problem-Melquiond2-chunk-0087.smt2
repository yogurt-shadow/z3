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
(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 92) 25) (* skoSXY (/ 288 125)))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 41) 5) (* skoSXY (/ 432 125))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 141) 50) (* skoSXY (/ 36 25)))))) (* skoX (* skoSXY (* skoSXY (+ (/ (- 1) 8) (* skoSXY (/ 18 125)))))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (/ (- 72) 25))))))))) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1))) skoY) (and (not (<= skoY 1)) (and (not (<= skoX (/ 3 2))) (and (not (<= skoSXY 0)) (and (not (<= 2 skoX)) (not (<= (/ 33 32) skoY)))))))))
(check-sat)
(exit)
