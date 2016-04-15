(ns hm.algs
  (require [adt.sweet :refer :all]
           [hm.ast :refer :all]
           [hm.type :refer :all]
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
        (TArrow args1 rtn1) (match mono2
                              (TArrow args2 rtn2)
                              (let [cs (reduce (fn [cs [m1 m2]]
                                                 (>=> [m1 m2] cs))
                                               cs
                                               (zipvec (conj args1 rtn1)
                                                       (conj args2 rtn2)))]
                                (unify subrule cs))
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
  (letfn [(binary-op [loprand roprand mono]
            (let [[cs1 l-mono] (algs env loprand)
                  [cs2 r-mono] (algs env roprand)
                  cs [[l-mono mono]
                      [r-mono mono]]]
              [(concatv cs cs1 cs2) mono]))]
    (match expr
      (EVar n) (let [t (if (contains? env n)
                         (instantiate (env n))
                         (throw-unbound-exp n))]
                 [[] t])
      (ELit lit) (let [lit-mono (match lit
                                  (LInt _) (TPrm PInt)
                                  (LBool _) (TPrm PBool)
                                  (LString _) (TPrm PString))]
                   [[] lit-mono])
      (EAbs vname expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                              new-env  (env-replace [vname (Mono fresh-tv)] env)
                              [cs mono] (algs new-env expr)]
                          [cs (TFun fresh-tv mono)])
      (EFun vnames body) (let [fresh-tvs (mapv (fn [_] (TVar (pick-fresh-tvname))) vnames)
                               fn-env    (reduce (fn [env [n t]]
                                                   (env-replace [n (Mono t)] env))
                                                 env
                                                 (zipvec vnames
                                                         fresh-tvs))
                               [cs b-mono] (algs fn-env body)]
                           [cs (TArrow fresh-tvs b-mono)])
      (EApp lexpr rexpr) (let [[cs1 mono1] (algs env lexpr)
                               [cs2 mono2] (algs env rexpr)
                               fresh-tv (TVar (pick-fresh-tvname))]
                           [(concatv (>=> [mono1 (TFun mono2 fresh-tv)] cs1) cs2) fresh-tv])
      (ECall fn-expr args) (let [[fn-cs fn-mono] (algs env fn-expr)
                                 arg-monos (mapv (fn [arg] (let [[cs t] (algs env arg)
                                                                 s (unify {} cs)]
                                                             (submono s t)))
                                                 args)
                                 fresh-tv  (TVar (pick-fresh-tvname))]
                             (match fn-mono
                               (TArrow params return)
                               (if (not= (count params) (count args))
                                 (throw-unexpected-number-args-exp expr)
                                 [(>=> [fn-mono (TArrow arg-monos fresh-tv)] fn-cs) fresh-tv])
                               (TVar n)
                               [(>=> [fn-mono (TArrow arg-monos fresh-tv)] fn-cs) fresh-tv]
                               :else (throw-expected-func-exp fn-expr)))
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
      (ETimes lnum rnum) (binary-op lnum rnum (TPrm PInt))
      (EAdd lnum rnum) (binary-op lnum rnum (TPrm PInt))
      (EIsZero num) (let [[cs t] (algs env num)]
                      [(>=> [t (TPrm PInt)] cs) (TPrm PBool)])
      (EIf p c a) (let [[cs1 p-mono] (algs env p)
                        [cs2 c-mono] (algs env c)
                        [cs3 a-mono] (algs env a)
                        cs [[p-mono (TPrm PBool)] [c-mono a-mono]]]
                    [(concatv cs cs1 cs2 cs3) a-mono])
      (EFix abs) (let [fresh-tv (TVar (pick-fresh-tvname))
                       [cs t] (algs env abs)]
                   [(>=> [t (TFun fresh-tv fresh-tv)] cs) fresh-tv])
      (EId expr) (let [fresh-tv (TVar (pick-fresh-tvname))
                       [cs t] (algs env expr)]
                   [(>=> [t fresh-tv] cs) fresh-tv])
      (ENot bool) (let [[cs t] (algs env bool)]
                    [(>=> [t (TPrm PBool)] cs) (TPrm PBool)])
      (EAnd lbool rbool) (binary-op lbool rbool (TPrm PBool))
      (EEq lexpr rexpr) (let [[cs1 l-mono] (algs env lexpr)
                              [cs2 r-mono] (algs env rexpr)
                              cs [[l-mono r-mono]]]
                          [(concatv cs cs1 cs2) (TPrm PBool)])
      (ECompose lfun rfun) (let [tva (TVar (pick-fresh-tvname))
                                 tvb (TVar (pick-fresh-tvname))
                                 tvc (TVar (pick-fresh-tvname))
                                 [cs1 l-mono] (algs env lfun)
                                 [cs2 r-mono] (algs env rfun)
                                 cs  [[l-mono (TFun tvb tvc)]
                                      [r-mono (TFun tva tvb)]]]
                             [(concatv cs cs1 cs2) (TFun tva tvc)])
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
                            [(concatv l-cs r-cs) (TPair l-mono r-mono)]))))

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
