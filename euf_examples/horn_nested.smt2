;; Nested Horn premises through a shared function symbol.
;;
;; F is shared, G is A-local. The outer congruence F(G(x)) = F(G(y)) would
;; be summarized with the boundary applications F(G(x)), F(G(y)) - not
;; shared because of G - so the run passes through it and inherits the
;; premise x = y of the inner (A-local) congruence G(x) = G(y):
;;
;;     (= x y)  ->  (= u v)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_nested_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U)
(declare-const y U)
(declare-const u U)
(declare-const v U)
(declare-fun F (U) U)
(declare-fun G (U) U)
(set-itp-group A)
(assert (= u (F (G x))))
(assert (= v (F (G y))))
(set-itp-group B)
(assert (= x y))
(assert (not (= u v)))
(assert (= (F x) x))
(check-sat)
