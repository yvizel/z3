;; iuc (b = c)

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log proof_46.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)
(declare-const e A)
(declare-fun F (A A) A)

(set-itp-group A)
(assert (not (= (F a b) (F c d))))

(set-itp-group B)
(assert (and (= a c) (= b d) ))

(check-sat)
;(get-proof)
