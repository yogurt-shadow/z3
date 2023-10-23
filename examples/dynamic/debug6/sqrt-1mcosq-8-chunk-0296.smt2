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
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ (/ (- 1) 2) (* skoY (* skoY (+ (/ 1 24) (* skoY (* skoY (+ (/ (- 1) 720) (* skoY (* skoY (+ (/ 1 40320) (* skoY (* skoY (+ (/ (- 1) 3628800) (* skoY (* skoY (+ (/ 1 479001600) (* skoY (* skoY (+ (/ (- 1) 87178291200) (* skoY (* skoY (+ (/ 1 20922789888000) (* skoY (* skoY (+ (/ (- 1) 6402373705728000) (* skoY (* skoY (+ (/ 1 2432902008176640000) (* skoY (* skoY (/ (- 1) 1124000727777607680000))))))))))))))))))))))))))))))))) (- 1)) (and (<= (* skoY (* skoY (+ 1 (* skoY (* skoY (+ (/ (- 1) 3) (* skoY (* skoY (+ (/ 2 45) (* skoY (* skoY (+ (/ (- 1) 315) (* skoY (* skoY (+ (/ 2 14175) (* skoY (* skoY (+ (/ (- 2) 467775) (* skoY (* skoY (+ (/ 4 42567525) (* skoY (* skoY (+ (/ (- 1) 638512875) (* skoY (* skoY (+ (/ 2 97692469875) (* skoY (* skoY (+ (/ (- 2) 9280784638125) (* skoY (* skoY (+ (/ 4 2143861251406875) (* skoY (* skoY (+ (/ (- 60787) 4496002911110430720000) (* skoY (* skoY (+ (/ 5611 67440043666656460800000) (* skoY (* skoY (+ (/ (- 8839) 20084871186542415052800000) (* skoY (* skoY (+ (/ 239 118357276634982088704000000) (* skoY (* skoY (+ (/ (- 137) 16967699178391032236605440000) (* skoY (* skoY (+ (/ 131 4666117274057533865066496000000) (* skoY (* skoY (+ (/ (- 197) 2342536687741696298196664320000000) (* skoY (* skoY (+ (/ 1 4685073375483392596393328640000000) (* skoY (* skoY (+ (/ (- 47) 105176293377005638102417617715200000000) (* skoY (* skoY (+ (/ 1 1367291813901073295331429030297600000000) (* skoY (* skoY (/ (- 1) 1263377636044591724886240423994982400000000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) 0) (and (<= skoY (+ (/ (- 1) 5) (* pi (/ 1 2)))) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= (/ 1 10) skoX) (not (<= skoY skoX)))))))))
(check-sat)
(exit)
