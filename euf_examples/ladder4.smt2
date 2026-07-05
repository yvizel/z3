;; Alternating A/B equality ladder, 4 steps: step i forces x_(i-1) = x_i
;; either directly or through the step-local y_i (odd steps A, even B);
;; B denies x_0 = x_N. Theory (EUF transitivity/congruence) lemmas over
;; mixed A/B chains.
;;
;; Minimal instance whose proof contains a deletion; historic repro of the
;; trim id/trail misalignment bug (now fixed).

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log ladder4_proof.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort U)
(declare-const x0 U)
(declare-const x1 U)
(declare-const x2 U)
(declare-const x3 U)
(declare-const x4 U)
(declare-const y1 U)
(declare-const y2 U)
(declare-const y3 U)
(declare-const y4 U)

(set-itp-group A)
(assert (and
          (or (= x0 x1) (= x0 y1))
          (or (not (= x0 y1)) (= y1 x1))
          (or (= x2 x3) (= x2 y3))
          (or (not (= x2 y3)) (= y3 x3))
        ))

(set-itp-group B)
(assert (and
          (or (= x1 x2) (= x1 y2))
          (or (not (= x1 y2)) (= y2 x2))
          (or (= x3 x4) (= x3 y4))
          (or (not (= x3 y4)) (= y4 x4))
          (not (= x0 x4))
        ))

(check-sat)
