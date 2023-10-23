(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Anastasiia Izycheva, Eva Darulova
Generated on: 2020-09-11
Generator: Pine (using Z3 Python API)
Application: Check inductiveness of a loop invariant
Target solver: Z3

These benchmarks were generated while developing the tool Pine [1], which uses
CVC4/Z3 to check inductiveness of invariants. The work is described in [2].

[1] https://github.com/izycheva/pine
[2] A.Izycheva, E.Darulova, H.Seidl, SAS'20, "Counterexample- and Simulation-Guided Floating-Point Loop Invariant Synthesis"

 Loop:
   u' := u + 0.01 * v
   v' := v + 0.01 * (-0.5 * v - 9.81 * u)

 Input ranges:
   u in [0.0,0.0]
   v in [2.0,3.0]

 Invariant:
   -0.09*u + 0.01*v + 1.0*u^2 + 0.04*u*v + 0.11*v^2 <= 1.66
 and
   u in [-1.2,1.3]
   v in [-3.9,3.7]

 Query: Loop and Invariant and not Invariant'
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun u! () Real)
(declare-fun v! () Real)
(declare-fun u () Real)
(declare-fun v () Real)
(assert
 (let ((?x99 (+ (* (* (/ 1.0 25.0) u!) v!) (+ (* (* (/ 11.0 100.0) v!) v!) (* (- (/ 9.0 100.0)) u!)))))
 (let (($x153 (and (<= (- (/ 6.0 5.0)) u!) (>= (/ 13.0 10.0) u!) (<= (- (/ 39.0 10.0)) v!) (>= (/ 37.0 10.0) v!))))
 (let (($x230 (and $x153 (>= (/ 83.0 50.0) (+ (* (/ 1.0 100.0) v!) (+ (* (* 1.0 u!) u!) ?x99))) )))
 (let (($x147 (and (= u! (+ u (* (/ 1.0 100.0) v))) (= v! (+ v (* (/ 1.0 100.0) (- (* (- (/ 1.0 2.0)) v) (* (/ 981.0 100.0) u))))))))
 (let ((?x289 (+ (* (* (/ 1.0 25.0) u) v) (+ (* (* (/ 11.0 100.0) v) v) (* (- (/ 9.0 100.0)) u)))))
 (let ((?x271 (* (/ 1.0 100.0) v)))
 (let (($x27 (and (<= (- (/ 6.0 5.0)) u) (>= (/ 13.0 10.0) u) (<= (- (/ 39.0 10.0)) v) (>= (/ 37.0 10.0) v))))
 (let (($x86 (and $x27 (>= (/ 83.0 50.0) (+ ?x271 (+ (* (* 1.0 u) u) ?x289))) )))
 (and $x86 $x147 (not $x230)))))))))))
(check-sat)
(exit)
