(set-logic QF_NRA)

(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (and a (not b)))

(check-sat)
(get-model)
