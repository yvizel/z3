;; iuc (b = c)

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log proof_43.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)
(declare-const e A)
(declare-fun F (A) A)

(set-itp-group A)
(assert (and 
          (or (not (= (F b) (F d))) (= a b) (= a d))
          (or (not (= (F a) (F b)) ) (not (= (F a) (F d))))
          (or (not (= (F a) (F d))) (not (= (F b) (F d))) )
          (not (= (F a) (F d)))
        )
)

(set-itp-group B)
(assert (and (= b c) (= (F c) (F d))))

(check-sat)
