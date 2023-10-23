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
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoT (+ (* skoB (/ 157 100)) (* skoT (+ (- 1) skoB)))) (* skoB skoA)) (and (not (<= (* skoT (+ (* skoB (/ (- 157) 100)) (* skoT (+ 1 (* skoB (- 1)))))) (* skoB (* skoA (- 1))))) (and (not (<= skoB skoA)) (and (not (<= 2 skoB)) (and (not (<= skoA 0)) (not (<= skoT (/ 3 2)))))))))
(check-sat)
(exit)
