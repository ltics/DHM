(ns hm.algw
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.subst :refer :all]))

(defn occurs
  "prevents inference of infinite types
   a ~ a -> b => a ~ ((... -> b) -> b) -> b"
  [tvname t]
  (match t
    (TVar name) (= tvname name)
    (TFun lmono rmono) (or (occurs tvname lmono) (occurs tvname rmono))
    :else false))

(defn unify
  "unification of two monotypes, return the subrule t ~ t' : s
   the subrule also is mgu(t1, t2)"
  [mono1 mono2]
  (match mono1
    (TPrm p1) (match mono2
                (TPrm p2) (if (= p1 p2) {} nil))
    (TVar n1) (when-not (occurs n1 mono2) {n1 mono2})
    (TFun lm1 rm1) (match mono2
                     (TFun lm2 rm2) (when-let [s1 (unify lm1 lm2)]
                                      (let [s (partial submono s1)]
                                        (when-let [s2 (unify (s rm1)
                                                             (s rm2))]
                                          (compose s2 s1)))))
    :else (match mono2
            (TVar n2) (when-not (occurs n2 mono1) {n2 mono1}))))

