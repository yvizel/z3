;; Horn summary with an A-local argument term.
;;
;; F and a are A-local; x, y, u, v are shared. The congruence F(a) = F(y)
;; is justified by the mixed argument path a ~A x ~B y. The premise of the
;; A-run u ~ v must be the boundary equality x = y (not a = y, which would
;; expose the A-local a):
;;
;;     (= x y)  ->  (= u v)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_local_arg_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const a U)
(declare-const x U)
(declare-const y U)
(declare-const u U)
(declare-const v U)
(declare-fun F (U) U)
(set-itp-group A)
(assert (= u (F a)))
(assert (= a x))
(assert (= v (F y)))
(set-itp-group B)
(assert (= x y))
(assert (not (= u v)))
(check-sat)
