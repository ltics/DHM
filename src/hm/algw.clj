(ns hm.algw
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.env :refer :all]
           [hm.subst :refer :all]
           [hm.error :refer :all]))

(defn unify
  "unification of two monotypes, return the subrule t ~ t' : s
   the subrule also is mgu(t1, t2), a most general unifier for t1 an t2
   {} stand for ⊥ and error msg stand for undefined
   unify(TVar 'a', TVar 'a') -> {}
   unify(TPrm PInt, TPrm PBool) -> types do not unify"
  [mono1 mono2]
  (let [match-m2-tvar #(match mono2
                        (TVar n2) (if-not (occurs n2 mono1)
                                    {n2 mono1}
                                    (throw-occurs-exp mono2 mono1))
                        :else (throw-unify-exp mono1 mono2))]
    (match mono1
      (TVar n1) (match mono2
                  (TVar n2) (if (= n1 n2) {} {n1 mono2})
                  ;; prevents inference of infinite types
                  ;; e.g. λf -> f f => a ~ a → b => a ~ ((… → b) → b) → b
                  :else (if-not (occurs n1 mono2)
                          {n1 mono2}
                          (throw-occurs-exp mono1 mono2)))
      (TPrm p1) (match mono2
                  (TPrm p2) (if (= p1 p2)
                              {}
                              (throw-unify-exp mono1 mono2))
                  :else (match-m2-tvar))
      (TFun lm1 rm1) (match mono2
                       (TFun lm2 rm2) (let [s1 (unify lm1 lm2)
                                            s  (partial submono s1)
                                            s2 (unify (s rm1)
                                                      (s rm2))]
                                        (compose s2 s1))
                       :else (match-m2-tvar))
      (TList m1) (match mono2
                   (TList m2) (unify m1 m2)
                   :else (match-m2-tvar))
      (TPair lm1 rm1) (match mono2
                        (TPair lm2 rm2) (let [s1 (unify lm1 lm2)
                                              s  (partial submono s1)
                                              s2 (unify (s rm1)
                                                        (s rm2))]
                                          (compose s2 s1))
                        :else (match-m2-tvar))
      :else (throw-unify-exp mono1 mono2))))

(defn algw
  "type inference procedure
   algw(env, expr) -> (subrule, type)"
  [env expr]
  (match expr
    (EVar n) (let [t (if (contains? env n)
                       (instantiate (env n))
                       (throw-unbound-exp n))]
               [{} t])
    (ELit lit) (let [lit-mono (match lit
                                (LInt _) (TPrm PInt)
                                (LBool _) (TPrm PBool)
                                (LString _) (TPrm PString))]
                 [{} lit-mono])
    (EAbs vname expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                            ;; (algw (env-replace [vname (generalize env fresh-tv)] env) expr)
                            ;; it is meaningless to allow polymorphic lambda abstraction
                            ;; e.g. expr: λid -> pair (id true) (id 3) and the assumptions will be {id ∀a. a}
                            ;; the subexpr (id true) will just be unify(instantiate(∀a. a), bool -> b) => unify(a, bool -> b)
                            ;; but in let-polymorphism it will be something like unify(a -> a, bool -> b)
                            ;; it just can not determine the return type of b
                            ;; so the type of λid -> pair (id true) (id 3) in generalize lambda abstraction
                            ;; will be something like a -> (e * h) just not make any sense
                            [subrule mono] (algw (env-replace [vname (Mono fresh-tv)]
                                                              env)
                                                 expr)
                            abs-mono (TFun (submono subrule fresh-tv) mono)]
                        [subrule abs-mono])
    (EApp lexpr rexpr) (let [[subrule1 mono1] (algw env lexpr)
                             [subrule2 mono2] (algw (subenv subrule1 env) rexpr)
                             fresh-tv (TVar (pick-fresh-tvname))]
                         (try (let [subrule3 (unify (submono subrule2 mono1)
                                                    (TFun mono2 fresh-tv))]
                                [(compose subrule3 (compose subrule2 subrule1))
                                 (submono subrule3 fresh-tv)])
                              (catch Exception e
                                (throw-innerexpr-exp e expr))))
    (ELet n expr body) (let [[subrule1 e-mono] (algw env expr)
                             s1-env (subenv subrule1 env)
                             [subrule2 b-mono] (algw (env-replace [n (generalize s1-env e-mono)] s1-env) body)]
                         [(compose subrule2 subrule1) b-mono])
    (ELetRec n expr body) (let [fresh-tv (TVar (pick-fresh-tvname))
                                ext-env  (env-replace [n (Mono fresh-tv)] env)
                                [subrule1 e-mono] (algw ext-env expr)
                                subrule2 (unify fresh-tv e-mono)
                                s2-env   (subenv subrule2 ext-env)
                                [subrule3 b-mono] (algw (env-replace [n (generalize s2-env e-mono)] s2-env) body)]
                            [(compose subrule3 (compose subrule2 subrule1)) b-mono])
    :else (throw-unknown-exp expr)))

(defn infer
  "type inference wrapper, infer(env, expr) -> type, basicly a monotype returned"
  [env expr]
  (try (let [[_ mono] (algw env expr)]
         mono)
       (catch Exception e
         (TError (.getMessage e)))
       (finally (reset! fresh-state 0))))
