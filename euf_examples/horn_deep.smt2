;; Three nested A-local functions: F(G(H(x))) = F(G(H(y))).
;; Every congruence on the run is HORN (no shared application exists);
;; the single premise x = y propagates through all three levels.
;;   expected: (=> (= x y) (= u v))
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_deep_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U) (declare-const y U) (declare-const u U) (declare-const v U)
(declare-fun F (U) U) (declare-fun G (U) U) (declare-fun H (U) U)
(set-itp-group A)
(assert (= u (F (G (H x)))))
(assert (= v (F (G (H y)))))
(set-itp-group B)
(assert (= x y))
(assert (not (= u v)))
(check-sat)
