;; Congruence whose endpoint terms are B-only.
;;
;; c is B-local, so F(a,c) and F(b,c) cannot appear in the summary even
;; though F, a, b are shared. The only A contribution to the congruence
;; F(a,c) = F(b,c) is the argument equality:
;;
;;     (= a b)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log boundary_bonly_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const e U)
(declare-const p U)
(declare-const q U)
(declare-fun F (U U) U)
(set-itp-group A)
(assert (= a b))
(assert (= (F d d) e))
(set-itp-group B)
(assert (= p (F a c)))
(assert (= (F b c) q))
(assert (not (= p q)))
(check-sat)
