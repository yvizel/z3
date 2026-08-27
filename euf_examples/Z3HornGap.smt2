;; Minimal completeness gap in the EUF interpolator on Z3 branch `replay`.
;;
;; F is A-local.  The constants x, y, u, and v are shared.  The shared Craig
;; interpolant is the equality Horn clause
;;
;;     (= x y)  ->  (= u v)
;;
;; The current egraph path summarizer instead exposes A-local F:
;;
;;     (and (= u (F x)) (= v (F y)))
;;
;; To reproduce with a debug build of the branch:
;;
;;   z3 Z3HornGap.smt2
;;   z3 Z3HornGap.proof.smt2 \
;;     solver.proof.trim=true \
;;     solver.proof.interpolate=true \
;;     solver.proof.itp_labeling=mcmillan \
;;     solver.proof.check_interpolant=true -v:2
;;
;; The first two semantic checks pass, but the vocabulary check reports:
;;
;;   interpolant uses non-shared symbol F
;;   check interpolant shared symbols only: FAILED

(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log Z3HornGap.proof.smt2)
(set-option :solver.proof.interpolate_log true)

(declare-sort U)
(declare-const x U)
(declare-const y U)
(declare-const u U)
(declare-const v U)
(declare-fun F (U) U)

(set-itp-group A)
(assert (= u (F x)))
(assert (= v (F y)))

(set-itp-group B)
(assert (= x y))
(assert (not (= u v)))

(check-sat)
