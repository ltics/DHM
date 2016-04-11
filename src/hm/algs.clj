(ns hm.algs
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.subst :refer :all]
           [hm.env :refer :all]
           [hm.error :refer :all]))

(defn unify
  "find a substitution satisfied constraints"
  [subrule cs]
  (if (empty? cs)
    subrule
    (let [[[mono1 mono2] & cs] cs
          cs            (vec cs)
          match-m2-tvar #(match mono2
                          (TVar n2) (if-not (occurs n2 mono1)
                                      (let [subst {n2 mono1}]
                                        (unify (compose subst subrule)
                                               (subconstraints subst cs)))
                                      (throw-occurs-exp mono1 mono2))
                          :else (throw-unify-exp mono1 mono2))]
      (match mono1
        (TVar n1) (match mono2
                    (TVar n2) (when (= n1 n2)
                                (unify subrule cs))
                    :else (if-not (occurs n1 mono2)
                            (let [subst {n1 mono2}]
                              (unify (compose subst subrule)
                                     (subconstraints subst cs)))
                            (throw-occurs-exp mono1 mono2)))
        (TFun lm1 rm1) (match mono2
                         (TFun lm2 rm2) (unify subrule
                                               (>=> [lm1 lm2]
                                                    (>=> [rm1 rm2] cs)))
                         :else (match-m2-tvar))))))

(defn algs
  "algs(env, expr) -> (constraints, type)"
  [env expr]
  (match expr
    (EVar n) (let [t (if (contains? env n)
                       (instantiate (env n))
                       (throw-unbound-exp n))]
               [[] t])
    (EAbs vname expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                            new-env  (env-replace [vname (Mono fresh-tv)] env)
                            [cs mono] (algs new-env expr)]
                        [cs (TFun fresh-tv mono)])
    (EApp lexpr rexpr) (let [[cs1 mono1] (algs env lexpr)
                             [cs2 mono2] (algs env rexpr)
                             fresh-tv (TVar (pick-fresh-tvname))]
                         [(concat (>=> [mono1 (TFun mono2 fresh-tv)] cs2) cs1) fresh-tv])
    (ELet n expr body) (let [[cs1 e-mono] (algs env expr)
                             subrule (unify {} cs1)
                             s-env   (subenv subrule env)
                             e-poly  (generalize s-env
                                                 (submono subrule e-mono))
                             new-env (env-replace [n e-poly] s-env)
                             [cs2 b-mono] (algs new-env body)]
                         [(concat cs2 cs1) b-mono])))

(defn infer
  "infer(env, expr) -> type"
  [env expr]
  (try (let [[cs mono] (algs env expr)
             s (unify {} cs)]
         (submono s mono))
       (catch Exception e
         (TError (.getMessage e)))
       (finally (reset! fresh-state 0))))
