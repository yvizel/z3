;; iuc (b = d)

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-fun f (A) A)

(assert (and (not (= (f a) (f b)) ) ))

(assert (= a b))
(check-sat)
