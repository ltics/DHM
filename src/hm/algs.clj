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
                    (TVar n2) (if (= n1 n2)
                                (unify subrule cs)
                                (let [subst {n1 mono2}]
                                  (unify (compose subst subrule)
                                         (subconstraints subst cs))))
                    :else (if-not (occurs n1 mono2)
                            (let [subst {n1 mono2}]
                              (unify (compose subst subrule)
                                     (subconstraints subst cs)))
                            (throw-occurs-exp mono1 mono2)))
        (TPrm p1) (match mono2
                    (TPrm p2) (if (= p1 p2)
                                (unify subrule cs)
                                (throw-unify-exp mono1 mono2))
                    :else (match-m2-tvar))
        (TFun lm1 rm1) (match mono2
                         (TFun lm2 rm2) (unify subrule
                                               (>=> [lm1 lm2]
                                                    (>=> [rm1 rm2] cs)))
                         :else (match-m2-tvar))
        (TList m1) (match mono2
                     (TList m2) (unify subrule
                                       (>=> [m1 m2] cs))
                     :else (match-m2-tvar))
        (TPair lm1 rm1) (match mono2
                          (TPair lm2 rm2) (unify subrule
                                                 (>=> [lm1 lm2]
                                                      (>=> (rm1 rm2) cs)))
                          :else (match-m2-tvar))))))

(defn algs
  "algs(env, expr) -> (constraints, type)"
  [env expr]
  (match expr
    (EVar n) (let [t (if (contains? env n)
                       (instantiate (env n))
                       (throw-unbound-exp n))]
               [[] t])
    (ELit lit) (let [lit-mono (match lit
                                (LInt _) (TPrm PInt)
                                (LBool _) (TPrm PBool))]
                 [[] lit-mono])
    (EAbs vname expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                            new-env  (env-replace [vname (Mono fresh-tv)] env)
                            [cs mono] (algs new-env expr)]
                        [cs (TFun fresh-tv mono)])
    (EApp lexpr rexpr) (let [[cs1 mono1] (algs env lexpr)
                             [cs2 mono2] (algs env rexpr)
                             fresh-tv (TVar (pick-fresh-tvname))]
                         [(concatv (>=> [mono1 (TFun mono2 fresh-tv)] cs1) cs2) fresh-tv])
    (ELet n expr body) (let [[cs1 e-mono] (algs env expr)
                             subrule (unify {} cs1)
                             s-env   (subenv subrule env)
                             e-poly  (generalize s-env
                                                 (submono subrule e-mono))
                             new-env (env-replace [n e-poly] s-env)
                             [cs2 b-mono] (algs new-env body)]
                         [(concatv cs1 cs2) b-mono])
    (ELetRec n expr body) (let [fresh-tv (TVar (pick-fresh-tvname))
                                ext-env  (env-replace [n (Mono fresh-tv)] env)
                                [cs1 e-mono] (algs ext-env expr)
                                subrule  (unify {} cs1)
                                s-env    (subenv subrule ext-env)
                                e-poly   (generalize s-env (submono subrule e-mono))
                                new-env  (env-replace [n e-poly] s-env)
                                [cs2 b-mono] (algs new-env body)]
                            [(concatv cs1 cs2) b-mono])
    ;; in algs extra type rule can not just put in assumptions
    ;; should have explicit syntax definitions
    (ESucc num) (let [[cs t] (algs env num)]
                  [(>=> [t (TPrm PInt)] cs) (TPrm PInt)])
    (EPred num) (let [[cs t] (algs env num)]
                  [(>=> [t (TPrm PInt)] cs) (TPrm PInt)])
    (EIsZero num) (let [[cs t] (algs env num)]
                    [(>=> [t (TPrm PInt)] cs) (TPrm PBool)])
    (EIf p c a) (let [[cs1 p-mono] (algs env p)
                      [cs2 c-mono] (algs env c)
                      [cs3 a-mono] (algs env a)
                      cs [[p-mono (TPrm PBool)] [c-mono a-mono]]]
                  [(concatv cs cs1 cs2 cs3) a-mono])
    ENil [[] (Poly #{"a"} (TList (TVar "a")))]
    (ECons e l) (let [[cs1 e-mono] (algs env e)
                      [cs2 l-mono] (algs env l)
                      l-mono (instantiate l-mono)
                      cs     [[l-mono (TList e-mono)]]]
                  [(concatv cs cs1 cs2) l-mono])
    (EIsEmpty l) (let [[l-cs l-mono] (algs env l)
                       cs [l-mono (instantiate (Poly #{"a"} (TList (TVar "a"))))]]
                   [(>=> cs l-cs) (TPrm PBool)])
    (EPair lexpr rexpr) (let [[l-cs l-mono] (algs env lexpr)
                              [r-cs r-mono] (algs env rexpr)]
                          [(concatv l-cs r-cs) (TPair l-mono r-mono)])))

(defn infer
  "infer(env, expr) -> type"
  [env expr]
  (try (let [[cs mono] (algs env expr)
             s (unify {} cs)]
         (submono s mono))
       (catch Exception e
         (TError (format "%s in %s"
                         (.getMessage e)
                         (s-of-expr expr))))
       (finally (reset! fresh-state 0))))
