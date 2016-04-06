(ns hm.algw-test
  (require [acolfut.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.env :refer :all]
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
  (testing "inference normal types"
    (let [fun-id    (EAbs 0 (EVar 0))
          fun-true  (EAbs 0 (EAbs 1 (EVar 0)))
          fun-false (EAbs 0 (EAbs 1 (EVar 1)))
          e-true    (ELit (LBool true))
          e-false   (ELit (LBool false))
          e-1       (ELit (LInt 1))
          e-2       (ELit (LInt 2))
          expr0     (ELet 0 fun-id (EApp (EApp fun-false (EVar 0))
                                         (EApp (EApp (EVar 0) (EVar 0)) e-false)))
          expr1     (ELet "id" (EAbs "x" (EVar "x")) (EVar "id"))
          expr2     (ELet "id" (EAbs "x" (EVar "x")) (EApp (EVar "id") (EVar "id")))
          expr3     (ELet "id"
                          (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
                          (EApp (EVar "id") (EVar "id")))
          expr4     (ELet "id"
                          (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
                          (EApp (EApp (EVar "id") (EVar "id")) (ELit (LInt 3))))
          expr5     (ELet "id"
                          (EAbs "x" (EApp (EVar "x") (EVar "x")))
                          (EVar "id"))
          expr6     (EAbs "m" (ELet "y"
                                    (EVar "m")
                                    (ELet "x"
                                          (EApp (EVar "y") (ELit (LBool true)))
                                          (EVar "x"))))
          expr7     (EApp (ELit (LInt 3)) (ELit (LInt 3)))
          expr8     (EAbs "a"
                          (ELet "x"
                                (EAbs "b"
                                      (ELet "y"
                                            (EAbs "c" (EApp (EVar "a") (ELit (LInt 1))))
                                            (EApp (EVar "y") (ELit (LInt 3)))))
                                (EApp (EVar "x") (ELit (LInt 3)))))
          expr9     (EAbs "a" (EAbs "b"
                                    (EApp (EVar "b")
                                          (EApp (EVar "a")
                                                (EApp (EVar "a") (EVar "b"))))))]
      (is= (s-of-m (infer {} fun-id))
           "a -> a")
      (is= (s-of-m (infer {} fun-true))
           "b -> c -> b")
      (is= (s-of-m (infer {} fun-false))
           "d -> e -> e")
      (is= (s-of-m (infer {} e-true))
           (s-of-m (infer {} e-false))
           "bool")
      (is= (s-of-m (infer {} e-1))
           (s-of-m (infer {} e-2))
           "int")
      (is= (s-of-m (infer {} expr0)) "bool")
      (is= (s-of-m (infer {} expr1)) "q -> q")
      (is= (s-of-m (infer {} expr2)) "t -> t")
      (is= (s-of-m (infer {} expr3)) "x -> x")
      (is= (s-of-m (infer {} expr4)) "int")
      (is= (s-of-m (infer {} expr5)) "occurs check fails: E vs. E -> F in x x")
      (is= (s-of-m (infer {} expr6)) "(bool -> H) -> H")
      (is= (s-of-m (infer {} expr7)) "types do not unify: int vs. int -> I in 3 3")
      (is= (s-of-m (infer {} expr8)) "(int -> Q) -> Q")
      (is= (s-of-m (infer {} expr9)) "occurs check fails: U vs. U -> V in b (a (a b))")))
  (testing "inference recursion function types"
    (let [expr0 (ELetRec "factorial"
                         (EAbs "n"
                               (EApp (EApp (EApp (EVar "if")
                                                 (EApp (EVar "iszero")
                                                       (EVar "n")))
                                           (ELit (LInt 1)))
                                     (EApp (EApp (EVar "times")
                                                 (EVar "n"))
                                           (EApp (EVar "factorial")
                                                 (EApp (EVar "pred")
                                                       (EVar "n"))))))
                         (EVar "factorial"))
          expr1 (ELetRec "factorial"
                         (EAbs "n"
                               (EApp (EApp (EApp (EVar "if")
                                                 (EApp (EVar "iszero")
                                                       (EVar "n")))
                                           (ELit (LInt 1)))
                                     (EApp (EApp (EVar "times")
                                                 (EVar "n"))
                                           (EApp (EVar "factorial")
                                                 (EApp (EVar "pred")
                                                       (EVar "n"))))))
                         (EApp (EVar "factorial") (ELit (LInt 5))))]
      (is= (s-of-m (infer common-env expr0)) "int -> int")
      (is= (s-of-m (infer common-env expr1)) "int"))))
