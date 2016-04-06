(ns hm.env
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.subst :refer :all]))

;; environment is just mapping variable names to polytypes,
;; which is also called assumptions in some papers.

(defn env-of-list
  "get env from a list of variable name and polytype pairs"
  [l]
  (reduce (fn [env [vname poly]]
            (assoc env vname poly)) {} l))

(defn env-replace
  [[vname poly] env]
  (assoc env vname poly))

(defn get-ftvset-from-env
  "union of the free type variables of all polytypes from the range of env"
  [env]
  (reduce (fn [ftvset [_ poly]]
            (clojure.set/union ftvset (ftv poly))) #{} env))

(defn subst-env
  "substitute type variable binding (tvname:poly) with (tvname:subst(poly))"
  [subrule env]
  (->> env
       (map (fn [[vname poly]]
              [vname (subpoly subrule poly)]))
       (into {})))

(defn generalize
  "generalize monotype mono by applying universal quantification
   for all free type variables (ftv(mono) - (ftv(env))
   a -> b generalize to ∀a, b. a -> b
   e.g. the assumption Γ = {x : τ}
   generalize λy.x : σ → τ to ∀σ. σ → τ, but not to ∀σ,τ. σ → τ,
   because τ is free variable in Γ"
  [env mono]
  (Poly (clojure.set/difference (ftv (Mono mono))
                                (get-ftvset-from-env env))
        mono))

(defn instantiate
  "polytype to monotype, all quantified variables get replaced by fresh free type variables
   instantiate(∀a1 ... an . t) -> [a1/b1 ... an/bn]t where b1 ... bn are fresh"
  [t]
  (match t
    (Mono mono) mono
    (Poly tvnames mono) (let [subrule (reduce (fn [acc tvname]
                                                (assoc acc tvname (TVar (pick-fresh-tvname))))
                                              {} tvnames)]
                          (submono subrule mono))))

(def common-env
  {"true"    (Mono (TPrm PBool))
   "false"   (Mono (TPrm PBool))
   "zero"    (Mono (TPrm PInt))
   "iszero"  (Mono (TFun (TPrm PInt) (TPrm PBool)))
   "succ"    (Mono (TFun (TPrm PInt) (TPrm PInt)))
   "pred"    (Mono (TFun (TPrm PInt) (TPrm PInt)))
   "times"   (Mono (TFun (TPrm PInt) (TFun (TPrm PInt) (TPrm PInt))))
   "if"      (let [fresh-tv (TVar "a")]
               (Mono (TFun (TPrm PBool) (TFun fresh-tv (TFun fresh-tv fresh-tv)))))
   "fix"     (let [fresh-tv (TVar "b")]
               (Mono (TFun (TFun fresh-tv fresh-tv) fresh-tv)))
   "nil"     (Mono (TList (TVar "c")))
   "cons"    (let [fresh-tv (TVar "d")]
               (Mono (TFun fresh-tv (TFun (TList fresh-tv) (TList fresh-tv)))))
   "isempty" (Mono (TFun (TList (TVar "e")) (TPrm PBool)))
   "head"    (let [fresh-tv (TVar "f")]
               (Mono (TFun (TList fresh-tv) fresh-tv)))
   "tail"    (let [fresh-tv (TVar "g")]
               (Mono (TFun (TList fresh-tv) (TList fresh-tv))))
   "pair"    (let [fresh-tv1 (TVar "h")
                   fresh-tv2 (TVar "i")]
               (Mono (TFun fresh-tv1 (TFun fresh-tv2 (TPair fresh-tv1 fresh-tv2)))))})
