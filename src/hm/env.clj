(ns hm.env
  (require [adt.sweet :refer :all]
           [hm.type :refer :all]
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

(defn subenv
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

(def assumptions
  {"true"    (Mono (TPrm PBool))
   "false"   (Mono (TPrm PBool))
   "zero"    (Mono (TPrm PInt))
   "iszero"  (Mono (TFun (TPrm PInt) (TPrm PBool)))
   "succ"    (Mono (TFun (TPrm PInt) (TPrm PInt)))
   "pred"    (Mono (TFun (TPrm PInt) (TPrm PInt)))
   "times"   (Mono (TFun (TPrm PInt) (TFun (TPrm PInt) (TPrm PInt))))
   "add"     (Mono (TFun (TPrm PInt) (TFun (TPrm PInt) (TPrm PInt))))
   "plus"    (Mono (TArrow [(TPrm PInt) (TPrm PInt)] (TPrm PInt)))
   "and"     (Mono (TFun (TPrm PBool) (TFun (TPrm PBool) (TPrm PBool))))
   "not"     (Mono (TFun (TPrm PBool) (TPrm PBool)))
   "id"      (Poly #{"a"} (TFun (TVar "a") (TVar "a")))
   "const"   (Poly #{"a" "b"} (TFun (TVar "a") (TFun (TVar "b") (TVar "a"))))
   "eq"      (Poly #{"a"} (TFun (TVar "a") (TFun (TVar "a") (TPrm PBool))))
   "eqa"     (Poly #{"a"} (TArrow [(TVar "a") (TVar "a")] (TPrm PBool)))
   "compose" (Poly #{"a" "b" "c"} (TFun (TFun (TVar "b") (TVar "c"))
                                        (TFun (TFun (TVar "a") (TVar "b"))
                                              (TFun (TVar "a") (TVar "c")))))
   "if"      (Poly #{"a"} (TFun (TPrm PBool) (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))))
   "fix"     (Poly #{"a"} (TFun (TFun (TVar "a") (TVar "a")) (TVar "a")))
   "nil"     (Poly #{"a"} (TList (TVar "a")))
   "cons"    (Poly #{"a"} (TFun (TVar "a") (TFun (TList (TVar "a")) (TList (TVar "a")))))
   "consa"   (Poly #{"a"} (TArrow [(TVar "a") (TList (TVar "a"))] (TList (TVar "a"))))
   "map"     (Poly #{"a" "b"} (TFun (TFun (TVar "a") (TVar "b")) (TFun (TList (TVar "a")) (TList (TVar "b")))))
   "mapa"    (Poly #{"a" "b"} (TArrow [(TFun (TVar "a") (TVar "b")) (TList (TVar "a"))] (TList (TVar "b"))))
   "isempty" (Poly #{"a"} (TFun (TList (TVar "a")) (TPrm PBool)))
   "head"    (Poly #{"a"} (TFun (TList (TVar "a")) (TVar "a")))
   "tail"    (Poly #{"a"} (TFun (TList (TVar "a")) (TList (TVar "a"))))
   "pair"    (Poly #{"a" "b"} (TFun (TVar "a") (TFun (TVar "b") (TPair (TVar "a") (TVar "b")))))
   "paira"   (Poly #{"a" "b"} (TArrow [(TVar "a") (TVar "b")] (TPair (TVar "a") (TVar "b"))))
   "first"   (Poly #{"a" "b"} (TFun (TPair (TVar "a") (TVar "b")) (TVar "a")))
   "second"  (Poly #{"a" "b"} (TFun (TPair (TVar "a") (TVar "b")) (TVar "b")))
   "apply"   (Poly #{"a" "b"} (TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "b"))))
   "applya"  (Poly #{"a" "b"} (TArrow [(TFun (TVar "a") (TVar "b")) (TVar "a")] (TVar "b")))
   "applyaa" (Poly #{"a" "b"} (TArrow [(TArrow [(TVar "a")] (TVar "b")) (TVar "a")] (TVar "b")))
   "choose"  (Poly #{"a"} (TFun (TVar "a") (TFun (TVar "a") (TVar "a"))))
   "choosea" (Poly #{"a"} (TArrow [(TVar "a") (TVar "a")] (TVar "a")))})
