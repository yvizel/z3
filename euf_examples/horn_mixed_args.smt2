;; Boundary application that would embed an A-local symbol.
;;
;; F is shared, G is A-local. The congruence F(G(x),p) = F(G(y),q) has one
;; argument path that is entirely A-derivable only under the B premise x = y
;; (through the A-local G) and one that is B-derivable (p = q). Cutting the
;; run at F(G(x),p) / F(G(x),q) would expose G, so the run passes through:
;;
;;     (and (= x y) (= p q))  ->  (= u v)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log horn_mixed_args_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U)
(declare-const y U)
(declare-const p U)
(declare-const q U)
(declare-const u U)
(declare-const v U)
(declare-fun F (U U) U)
(declare-fun G (U) U)
(set-itp-group A)
(assert (= u (F (G x) p)))
(assert (= v (F (G y) q)))
(set-itp-group B)
(assert (= x y))
(assert (= p q))
(assert (not (= u v)))
(assert (= (F x x) x))
(check-sat)
