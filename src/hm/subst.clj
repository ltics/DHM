(ns hm.subst
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]))

;; substitution rule is just mapping type variable names to monotypes

(defn subrule-of-list
  "get subrule from a list of type variable name and monotype pairs"
  [l]
  (reduce (fn [subrule [tvname mono]]
            (assoc subrule tvname mono)) {} l))

(defn submono
  "substitute free type variables with monotypes in a monotype"
  [subrule t]
  (match t
         (TVar tvname) (if (contains? subrule tvname)
                         (subrule tvname)
                         (TVar tvname))
         (TFun lmono rmono) (TFun (submono subrule lmono)
                                  (submono subrule rmono))
         :else t))

(defn subpoly
  "substitute free type variables with monotypes in a polytype"
  [subrule t]
  (match t
         (Mono mono) (Mono (submono subrule mono))
         (Poly tvnames mono) (let [subrule (filter (fn [[tvname _]]
                                                     ((complement contains?) tvnames tvname))
                                                   subrule)]
                               (Poly tvnames (submono subrule mono)))))

(defn compose
  "compose subrule s2 @@ s1 = s2 (s1 t) just like function composition"
  [subrule2 subrule1]
  (merge subrule2
         (->> subrule1
              (map (fn [[tvname mono]]
                     [tvname (submono subrule2 mono)]))
              (into {}))))
