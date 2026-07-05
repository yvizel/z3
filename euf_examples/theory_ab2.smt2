;; Gamma through the summarizer: u=y is AB (A unit + B clause occurrence),
;; x=u is A-local, and the congruence F(x)=F(y) needs the mixed chain
;; x~u (A) ~y (gamma). Under hkp the summarized closure includes gamma, so
;; the lemma interpolant becomes a single shared equality; under mcmillan
;; the chain splits at the gamma boundary.
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log theory_ab2_proof.smt2)
(set-option :solver.proof.interpolate_log true)
(declare-sort U)
(declare-const x U)
(declare-const u U)
(declare-const y U)
(declare-fun F (U) U)
(set-itp-group A)
(assert (= x u))
(assert (= u y))
(set-itp-group B)
(assert (or (not (= u y)) (not (= (F x) (F y)))))
(check-sat)
