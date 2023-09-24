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
(assert (and (not (<= (* skoZ (* skoX 3)) (* skoY (* skoX (+ 15 (* skoX (* skoX 8))))))) (and (= (* skoZ skoZ) (+ 75 (* skoX (* skoX 80)))) (and (= (* skoY skoY) 3) (and (<= skoX 1) (and (<= 0 skoZ) (and (<= 0 skoY) (not (<= skoX 0)))))))))
(check-sat)
(exit)
