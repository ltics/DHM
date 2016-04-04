(ns hm.algw-test
  (require [acolfut.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.algw :refer :all]))

(deftest algw-test
  (testing "unification"
    (let [mono1 (TFun (TVar "a") PInt)
          mono2 (TFun (TVar "b") (TVar "b"))
          mono3 (TFun (TVar 1) (TVar 2))
          mono4 (TFun (TFun (TVar 2) (TVar 3)) (TVar 3))]
      (is= (unify mono1 mono2) {"a" PInt "b" PInt})
      (is= (unify mono3 mono4) {1 (TFun (TVar 3) (TVar 3))
                                2 (TVar 3)}))))
