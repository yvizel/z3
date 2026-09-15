;; Symbol colors come from the original input clauses, not the trimmed core.
;;
;; H occurs in B only in `(= (H e) e)`, which the refutation does not need
;; and the trimmer drops. H is nevertheless in L(B), so it is shared and
;; the run u ~ F(x)=F(y) ~ H(a)=H(b) ~ v is cut at the shared boundary
;; application (BOUNDARY), not carried through with a premise a = b.
;;   expected: (and (=> (= x y) (= u (H a))) (= v (H b)))
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log sym_from_input_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U) (declare-const y U) (declare-const a U) (declare-const b U)
(declare-const e U) (declare-const u U) (declare-const v U)
(declare-fun F (U) U) (declare-fun H (U) U)
(set-itp-group A)
(assert (= u (F x)))
(assert (= (F y) (H a)))
(assert (= (H b) v))
(set-itp-group B)
(assert (= x y))
(assert (= a b))
(assert (not (= u v)))
(assert (= (H e) e))
(check-sat)
