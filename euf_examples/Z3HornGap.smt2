;; Minimal completeness gap in the EUF interpolator on Z3 branch `replay`
;; (fixed: the summarizer now emits Horn clauses; see README.md).
;;
;; F is A-local.  The constants x, y, u, and v are shared.  The shared Craig
;; interpolant is the equality Horn clause
;;
;;     (= x y)  ->  (= u v)
;;
;; The egraph path summarizer used to cut the A-run u ~ F(x) ~ F(y) ~ v at
;; the congruence and expose the boundary applications, i.e. A-local F:
;;
;;     (and (= u (F x)) (= v (F y)))
;;
;; which failed the vocabulary check. It now keeps the run intact through
;; the congruence and turns its B-justified argument equality into the
;; premise of the run's clause.
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
;; Expected:
;;
;;   ; interpolant: (or (not (= x y)) (= u v))
;;   ; check A => interpolant: passed
;;   ; check interpolant /\ B unsat: passed
;;   ; check interpolant shared symbols only: passed

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
