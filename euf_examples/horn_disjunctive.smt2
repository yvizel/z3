;; Propositional layer over Horn lemmas: A does not know which of two
;; A-local applications u equals, so the refutation resolves two EUF
;; lemmas on an A-local atom. Each lemma's partial interpolant is a Horn
;; clause; the resolution combines them (McMillan: disjunction on an
;; A-local pivot).
;;   expected: valid interpolant over {x, y, z, u, v}; shape depends on labeling
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_disjunctive_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U) (declare-const y U) (declare-const z U) (declare-const u U) (declare-const v U)
(declare-fun F (U) U)
(set-itp-group A)
(assert (or (= u (F x)) (= u (F z))))
(assert (= v (F y)))
(set-itp-group B)
(assert (= x y))
(assert (= z y))
(assert (not (= u v)))
(check-sat)
