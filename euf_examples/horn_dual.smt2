;; Horn summary on the B side, negated.
;;
;; The violated disequality u != v is in A, so the lemma interpolant is the
;; negation of B's summary. F is B-local, so B's contribution is the Horn
;; clause (x = y) -> (u = v), and the interpolant is its negation:
;;
;;     (and (= x y) (not (= u v)))
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_dual_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U)
(declare-const y U)
(declare-const u U)
(declare-const v U)
(declare-fun F (U) U)
(set-itp-group A)
(assert (= x y))
(assert (not (= u v)))
(set-itp-group B)
(assert (= u (F x)))
(assert (= v (F y)))
(check-sat)
