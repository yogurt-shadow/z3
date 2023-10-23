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
   v' := v + 0.01 * (-0.5 * v - 9.81 * (u - (u*u*u)/6.0 + (u*u*u*u*u)/120.0))

 Input ranges:
   u in [0.0,0.0]
   v in [2.0,3.0]

 Invariant:
   -0.14*u + -0.04*v + 1.0*u^2 + 0.03*u*v + 0.1*v^2 <= 0.8
 and
   u in [-0.8,1.0]
   v in [-2.7,3.0]

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
 (let ((?x8 (+ (* (* (/ 3.0 100.0) u!) v!) (+ (* (* (/ 1.0 10.0) v!) v!) (* (- (/ 7.0 50.0)) u!)))))
 (let (($x70 (and (<= (- (/ 4.0 5.0)) u!) (>= 1.0 u!) (<= (- (/ 27.0 10.0)) v!) (>= 3.0 v!))))
 (let (($x9 (and $x70 (>= (/ 4.0 5.0) (+ (* (- (/ 1.0 25.0)) v!) (+ (* (* 1.0 u!) u!) ?x8))) )))
 (let ((?x88 (+ (- u (/ (* (* u u) u) 6.0)) (/ (* (* (* (* u u) u) u) u) 120.0))))
 (let (($x49 (and (= u! (+ u (* (/ 1.0 100.0) v))) (= v! (+ v (* (/ 1.0 100.0) (- (* (- (/ 1.0 2.0)) v) (* (/ 981.0 100.0) ?x88))))))))
 (let ((?x18 (+ (* (* (/ 3.0 100.0) u) v) (+ (* (* (/ 1.0 10.0) v) v) (* (- (/ 7.0 50.0)) u)))))
 (let ((?x37 (* (- (/ 1.0 25.0)) v)))
 (let (($x19 (>= 3.0 v)))
 (let (($x24 (and (and (<= (- (/ 4.0 5.0)) u) (>= 1.0 u) (<= (- (/ 27.0 10.0)) v) $x19) (>= (/ 4.0 5.0) (+ ?x37 (+ (* (* 1.0 u) u) ?x18))) )))
 (and $x24 $x49 (not $x9))))))))))))
(check-sat)
(exit)
