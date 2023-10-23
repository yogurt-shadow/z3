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
(declare-fun skoR () Real)
(declare-fun skoE () Real)
(declare-fun skoEA () Real)
(assert (let ((?v_0 (* skoX (/ (- 1) 4)))) (and (<= skoR 0) (and (<= (* skoX ?v_0) (+ 1 (* skoR (- 1)))) (and (<= (* skoX (+ 1 ?v_0)) skoR) (and (<= skoEA (/ 1 85070591730234615865843651857942052864)) (and (<= skoE (/ 1 32)) (and (<= (/ (- 1) 32) skoE) (and (<= (/ (- 1) 85070591730234615865843651857942052864) skoEA) (and (<= skoX 2) (and (<= skoR 3) (and (<= (/ 1 2) skoX) (<= 0 skoR)))))))))))))
(check-sat)
(exit)
