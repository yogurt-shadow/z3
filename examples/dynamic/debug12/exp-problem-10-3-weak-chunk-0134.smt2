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
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoCM1 (+ (- 6) (* skoCM1 12))) (- 1))) (and (not (<= (* skoCM1 (+ (+ (- 6) (* skoC (+ 72 (* skoC (+ (- 504) (* skoC (+ 2304 (* skoC (+ (- 6912) (* skoC (+ 13824 (* skoC (- 27648))))))))))))) (* skoCM1 (+ (- 12) (* skoC (+ 144 (* skoC (+ (- 1008) (* skoC (+ 4608 (* skoC (+ (- 13824) (* skoC 27648))))))))))))) (+ 1 (* skoC (+ (- 12) (* skoC (+ 84 (* skoC (+ (- 384) (* skoC (+ 1152 (* skoC (- 2304))))))))))))) (and (= (+ 1 (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 1)) (and (not (<= skoCM1 0)) (not (<= skoC 0)))))))))
(check-sat)
(exit)
