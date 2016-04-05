(ns hm.algw
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.env :refer :all]
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
                (TPrm p2) (if (= p1 p2) {} nil)
                (TVar n2) (when-not (occurs n2 mono1) {n2 mono1}))
    (TVar n1) (when-not (occurs n1 mono2) {n1 mono2})
    (TFun lm1 rm1) (match mono2
                     (TFun lm2 rm2) (when-let [s1 (unify lm1 lm2)]
                                      (let [s (partial submono s1)]
                                        (when-let [s2 (unify (s rm1)
                                                             (s rm2))]
                                          (compose s2 s1))))
                     (TVar n2) (when-not (occurs n2 mono1) {n2 mono1}))
    :else (match mono2
            (TVar n2) (when-not (occurs n2 mono1) {n2 mono1}))))

(defn algw
  "type inference procedure
   algw(env, expr) -> (subrule, type)"
  [env expr]
  (match expr
    (EVar n) (let [t (if (contains? env n)
                       (instantiate (env n))
                       TError)]
               [{} t])
    (ELit lit) (let [lit-mono (match lit
                                (LInt _) (TPrm PInt)
                                (LBool _) (TPrm PBool))]
                 [{} lit-mono])
    (EAbs vname expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                            [subrule mono] (algw (env-replace [vname (Mono fresh-tv)]
                                                              env)
                                                 expr)
                            abs-mono (TFun (submono subrule fresh-tv) mono)]
                        [subrule abs-mono])
    (EApp lexpr rexpr) (let [[subrule1 mono1] (algw env lexpr)
                             [subrule2 mono2] (algw (subst-env subrule1 env) rexpr)
                             fresh-tv (TVar (pick-fresh-tvname))]
                         (if-let [subrule3 (unify (submono subrule2 mono1)
                                                  (TFun mono2 fresh-tv))]
                           [(compose subrule3 (compose subrule2 subrule1))
                            (submono subrule3 fresh-tv)]
                           [{} TError]))
    (ELet n expr body) (let [[subrule1 e-mono] (algw env expr)
                             s1-env (subst-env subrule1 env)
                             [subrule2 b-mono] (algw (env-replace [n (generalize s1-env e-mono)] s1-env) body)]
                         [(compose subrule2 subrule1) b-mono])
    :else [{} TError]))

(defn infer
  "type inference wrapper, infer(env, expr) -> type, basicly a monotype returned"
  [env expr]
  (let [[_ mono] (algw env expr)]
    mono))
