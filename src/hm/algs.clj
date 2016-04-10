(ns hm.algs
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.subst :refer :all]
           [hm.error :refer :all]))

(defn unify
  [subst-env cs]
  (let [match-m2-tvar #(match mono2
                        (TVar n2) (if-not (occurs n2 mono1)
                                    (let [subst {n2 mono1}]
                                      (unify (compose subst subst-env)
                                             (subconstraints subst cs)))
                                    (throw-occurs-exp mono1 mono2))
                        :else (throw-unify-exp mono1 mono2))]
    (if (empty? cs)
      subst-env
      (let [[[mono1 mono2] & cs] cs
            cs (vec cs)]
        (match mono1
          (TVar n1) (match mono2
                      (TVar n2) (when (= n1 n2)
                                  (unify subst-env cs))
                      :else (if-not (occurs n1 mono2)
                              (let [subst {n1 mono2}]
                                (unify (compose subst subst-env)
                                       (subconstraints subst cs)))
                              (throw-occurs-exp mono1 mono2)))
          (TFun lm1 rm1) (match mono2
                           (TFun lm2 rm2) (unify env
                                                 (>=> [lm1 lm2]
                                                     (>=> [rm1 rm2] cs)))
                           :else (match-m2-tvar)))))))

(defn constraints
  [assump-env expr])
