;; Colorability label optimization demo: a theory chain and a propositional
;; chain in one conflict. The shared link u=y sits inside the congruence
;; lemma; the chain boundary atoms are shared but purely propositional.
;; With itp_labeling=mcmillan itp_label_opt=colorable, only u=y is promoted
;; to ab - the lemma summarizes to a single equality (like hkp) while the
;; chain pivots stay guard-free (like mcmillan). Plain hkp pays ab guards
;; on every chain boundary; plain mcmillan splits the lemma chain.

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log colorable_opt_proof.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort U)
(declare-const x U)
(declare-const u U)
(declare-const y U)
(declare-fun F (U) U)
(declare-const a0 U)
(declare-const b0 U)
(declare-const a1 U)
(declare-const b1 U)
(declare-const a2 U)
(declare-const b2 U)
(declare-const a3 U)
(declare-const b3 U)
(declare-const a4 U)
(declare-const b4 U)
(declare-const a5 U)
(declare-const b5 U)
(declare-const a6 U)
(declare-const b6 U)
(declare-const a7 U)
(declare-const b7 U)
(declare-const a8 U)
(declare-const b8 U)
(declare-const a9 U)
(declare-const b9 U)

(set-itp-group A)
(assert (and
          (= x u)
          (= u y)
          (= a0 b0)
          (or (not (= a0 b0)) (= a1 b1))
          (or (not (= a2 b2)) (= a3 b3))
          (or (not (= a3 b3)) (= a4 b4))
          (or (not (= a5 b5)) (= a6 b6))
          (or (not (= a6 b6)) (= a7 b7))
          (or (not (= a8 b8)) (= a9 b9))
        ))

(set-itp-group B)
(assert (and
          (or (not (= a1 b1)) (= a2 b2))
          (or (not (= a4 b4)) (= a5 b5))
          (or (not (= a7 b7)) (= a8 b8))
          (or (not (= u y)) (not (= (F x) (F y))) (not (= a9 b9)))
        ))

(check-sat)
