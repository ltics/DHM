(ns hm.algw-test
  (require [acolfut.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.algw :refer :all]))

(deftest algw-test
  (testing "unification"
    (let [mono1 (TFun (TVar "a") PInt)
          mono2 (TFun (TVar "b") (TVar "b"))]
      (is= (unify mono1 mono2) {"a" PInt "b" PInt}))))
