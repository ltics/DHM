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
    (TArrow monos mono) (TArrow (mapv #(submono subrule %) monos)
                                (submono subrule mono))
    (TList mono) (TList (submono subrule mono))
    (TPair lmono rmono) (TPair (submono subrule lmono)
                               (submono subrule rmono))
    :else t))

(defn subpoly
  "substitute free type variables with monotypes in a polytype"
  [subrule t]
  (match t
    (Mono mono) (Mono (submono subrule mono))
    (Poly tvnames mono) (let [subrule (->> subrule
                                           (filter (fn [[tvname _]]
                                                     ((complement contains?) tvnames tvname)))
                                           (into {}))]
                          (Poly tvnames (submono subrule mono)))))

(defn subconstraints
  [subrule cs]
  (mapv (fn [[l r]]
          [(submono subrule l) (submono subrule r)])
        cs))

(defn >=>
  [c cs]
  (-> c
      (cons cs)
      vec))

(defmacro concatv [& body]
  `(into [] (concat ~@body)))

(defmacro zipvec [& vecs]
  `(mapv (fn [& vals#] (vec vals#)) ~@vecs))

(defn compose
  "compose subrule s2 @@ s1 = s2 (s1 t) just like function composition"
  [subrule2 subrule1]
  (merge subrule2
         (->> subrule1
              (map (fn [[tvname mono]]
                     [tvname (submono subrule2 mono)]))
              (into {}))))

(defn ftv
  "return the set of free type variable names"
  [t]
  (match t
    (Mono mono) (match mono
                  (TVar tvname) #{tvname}
                  (TFun lmono rmono) (clojure.set/union (ftv (Mono lmono))
                                                        (ftv (Mono rmono)))
                  (TArrow monos mono) (apply clojure.set/union (map #(ftv (Mono %)) (conj monos mono)))
                  (TList mono) (ftv (Mono mono))
                  (TPair lmono rmono) (clojure.set/union (ftv (Mono lmono))
                                                         (ftv (Mono rmono)))
                  :else #{})
    (Poly tvnames mono) (clojure.set/difference (ftv (Mono mono)) tvnames)))

(defn occurs
  "prevents inference of infinite types
   a ~ a -> b => a ~ ((... -> b) -> b) -> b"
  [tvname t]
  #_(match t
      (TVar name) (= tvname name)
      (TFun lmono rmono) (or (occurs tvname lmono) (occurs tvname rmono))
      :else false)
  (contains? (ftv (Mono t)) tvname))
