(ns hm.env
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.subst :refer :all]))

;; environment is just mapping variable names to polytypes

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
   a -> b generalize to ∀a, b. a -> b"
  [env mono]
  (Poly (clojure.set/difference (ftv (Mono mono))
                                (get-ftvset-from-env env))
        mono))

(def fresh-state (atom 0))

(defn pick-fresh-tvname
  "pick up a unique type variable name"
  []
  (swap! fresh-state inc)
  (dec @fresh-state))

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
