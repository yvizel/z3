(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log complex_proof.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort S 0)
(declare-fun f (S S) S)
(declare-fun g (S) S)
(declare-fun h (S S) S)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun c () S)
(declare-fun d () S)
(declare-fun e () S)
(declare-fun p () S)
(declare-fun q () S)
(declare-fun u () S)
(declare-fun v () S)
(declare-fun w () S)

; ---- A part (CNF) ----
(set-itp-group A)
(assert (or (= (g a) b) (= p q)))
(assert (not (= p q)))
(assert (not (= (f (f (g a) b) (h c d)) e)))

; ---- B part ----
(set-itp-group B)
(assert (= (f b b) u))
(assert (= (h c d) v))
(assert (= (f u v) w))
(assert (= w e))

(check-sat)
