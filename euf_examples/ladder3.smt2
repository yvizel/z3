;; Alternating A/B equality ladder, 3 steps: step i forces x_(i-1) = x_i
;; either directly or through the step-local y_i (odd steps A, even B);
;; B denies x_0 = x_N. Theory (EUF transitivity/congruence) lemmas over
;; mixed A/B chains.
;;
;; Small enough to replay even before the trim id/trail alignment fix.

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log ladder3_proof.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort U)
(declare-const x0 U)
(declare-const x1 U)
(declare-const x2 U)
(declare-const x3 U)
(declare-const y1 U)
(declare-const y2 U)
(declare-const y3 U)

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
          (not (= x0 x3))
        ))

(check-sat)
