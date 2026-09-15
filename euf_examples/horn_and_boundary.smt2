;; HORN and BOUNDARY on the same run: u ~ F(x)=F(y) ~ H(a)=H(b) with
;; F A-local (HORN, premise x = y) and H shared (it occurs in B's
;; disequality, so it survives trimming): the run is cut at the shared
;; boundary application H(a).
;;   expected: (=> (= x y) (= u (H a)))
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_and_boundary_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U) (declare-const y U) (declare-const a U) (declare-const b U)
(declare-const u U)
(declare-fun F (U) U) (declare-fun H (U) U)
(set-itp-group A)
(assert (= u (F x)))
(assert (= (F y) (H a)))
(set-itp-group B)
(assert (= x y))
(assert (= a b))
(assert (not (= u (H b))))
(check-sat)
