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
   -0.93*u + 0.12*v + 1.0*u^2 + -0.07*u*v + 0.07*v^2 <= 1.08
 and
   u in [-0.5,1.7]
   v in [-4.6,3.0]

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
 (let ((?x38 (+ (* (* (- (/ 7.0 100.0)) u!) v!) (+ (* (* (/ 7.0 100.0) v!) v!) (* (- (/ 93.0 100.0)) u!)))))
 (let ((?x15 (* (/ 3.0 25.0) v!)))
 (let (($x74 (and (<= (- (/ 1.0 2.0)) u!) (>= (/ 17.0 10.0) u!) (<= (- (/ 23.0 5.0)) v!) (>= 3.0 v!))))
 (let (($x48 (and $x74 (>= (/ 27.0 25.0) (+ ?x15 (+ (* (* 1.0 u!) u!) ?x38))) )))
 (let (($x49 (and (= u! (+ u (* (/ 1.0 100.0) v))) (= v! (+ v (* (/ 1.0 100.0) (- (* (- (/ 1.0 2.0)) v) (* (/ 981.0 100.0) u))))))))
 (let ((?x283 (+ (* (* (- (/ 7.0 100.0)) u) v) (+ (* (* (/ 7.0 100.0) v) v) (* (- (/ 93.0 100.0)) u)))))
 (let (($x6 (>= 3.0 v)))
 (let (($x285 (and (and (<= (- (/ 1.0 2.0)) u) (>= (/ 17.0 10.0) u) (<= (- (/ 23.0 5.0)) v) $x6) (>= (/ 27.0 25.0) (+ (* (/ 3.0 25.0) v) (+ (* (* 1.0 u) u) ?x283))) )))
 (and $x285 $x49 (not $x48)))))))))))
(check-sat)
(exit)
