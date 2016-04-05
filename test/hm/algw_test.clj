(ns hm.algw-test
  (require [acolfut.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.algw :refer :all]))

(deftest algw-test
  (testing "unification"
    (let [mono1 (TFun (TVar "a") (TPrm PInt))
          mono2 (TFun (TVar "b") (TVar "b"))
          mono3 (TFun (TVar 1) (TVar 2))
          mono4 (TFun (TFun (TVar 2) (TVar 3)) (TVar 3))]
      (is= (unify mono1 mono2) {"a" (TPrm PInt) "b" (TPrm PInt)})
      (is= (unify mono3 mono4) {1 (TFun (TVar 3) (TVar 3))
                                2 (TVar 3)})))
  (testing "inference"
    (let [fun-id (EAbs 0 (EVar 0))
          fun-true (EAbs 0 (EAbs 1 (EVar 0)))
          fun-false (EAbs 0 (EAbs 1 (EVar 1)))
          e-true (ELit (LBool true))
          e-false (ELit (LBool false))
          e-1 (ELit (LInt 1))
          e-2 (ELit (LInt 2))
          expr0 (ELet 0 fun-id (EApp (EApp fun-false (EVar 0))
                                     (EApp (EApp (EVar 0) (EVar 0)) e-false)))]
      (is= (s-of-m (infer {} fun-id))
           "(a -> a)")
      (is= (s-of-m (infer {} fun-true))
           "(b -> (c -> b))")
      (is= (s-of-m (infer {} fun-false))
           "(d -> (e -> e))")
      (is= (s-of-m (infer {} e-true))
           (s-of-m (infer {} e-false))
           "bool")
      (is= (s-of-m (infer {} e-1))
           (s-of-m (infer {} e-2))
           "int")
      (is= (s-of-m (infer {} expr0)) "bool"))))
