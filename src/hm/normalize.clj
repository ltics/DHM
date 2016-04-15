(ns hm.normalize
  (require [adt.sweet :refer :all]
           [hm.type :refer :all]
           [hm.subst :refer :all]))

(defn normalize
  [t]
  (match t
    (Poly tvnames mono) (if (empty? tvnames)
                          (s-of-m mono)
                          (let [tvnames' (range 0 (count tvnames))
                                subrule  (->> (zipmap (sort tvnames) tvnames')
                                              (map (fn [[tvn tvn']] [tvn (TVar tvn')]))
                                              (into {}))]
                            (format "∀%s. %s"
                                    (->> tvnames'
                                         (map s-of-tvn)
                                         (clojure.string/join ","))
                                    (s-of-m (submono subrule mono)))))))

(defn s-of-t
  "string of types"
  [t]
  (match t
    (Poly _) (normalize t)
    :else (s-of-m t)))
