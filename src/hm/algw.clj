(ns hm.algw
  (require [adt.sweet :refer :all]
           [hm.syntax :refer :all]))

(defn occurs
  "prevents inference of infinite types
   a ~ a -> b => a ~ ((... -> b) -> b) -> b"
  [tvname t]
  (match t
    (TVar name) (= tvname name)
    (TFun lmono rmono) (or (occurs tvname lmono) (occurs tvname rmono))
    :else false))
