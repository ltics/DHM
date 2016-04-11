(ns hm.algs-test
  (require [acolfut.sweet :refer :all]
           [hm.syntax :refer :all]
           [hm.env :refer :all]
           [hm.algs :refer :all]))

(deftest algs-test
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
                                                (EApp (EVar "a") (EVar "b"))))))
          expr10    (ELet "g"
                          (EAbs "f" (ELit (LInt 5)))
                          (EApp (EVar "g") (EVar "g")))
          ;; λf -> λg -> λarg -> g (f arg)
          expr11    (EAbs "f"
                          (EAbs "g"
                                (EAbs "arg"
                                      (EApp (EVar "g")
                                            (EApp (EVar "f") (EVar "arg"))))))]
      (is= (s-of-m (infer {} fun-id))
           "a -> a")
      (is= (s-of-m (infer {} fun-true))
           "a -> b -> a")
      (is= (s-of-m (infer {} fun-false))
           "a -> b -> b")
      (is= (s-of-m (infer {} e-true))
           (s-of-m (infer {} e-false))
           "bool")
      (is= (s-of-m (infer {} e-1))
           (s-of-m (infer {} e-2))
           "int")
      (is= (s-of-m (infer {} expr0)) "bool")
      (is= (s-of-m (infer {} expr1)) "b -> b")
      (is= (s-of-m (infer {} expr2)) "c -> c")
      (is= (s-of-m (infer {} expr3)) "c -> c")
      (is= (s-of-m (infer {} expr4)) "int")
      (is= (s-of-m (infer {} expr5)) "occurs check fails: a vs. a -> b")
      (is= (s-of-m (infer {} expr6)) "(bool -> b) -> b")
      (is= (s-of-m (infer {} expr7)) "types do not unify: int vs. int -> a")
      (is= (s-of-m (infer {} expr8)) "(int -> h) -> h")
      (is= (s-of-m (infer {} expr9)) "occurs check fails: d vs. d -> e")
      (is= (s-of-m (infer {} expr10)) "int")
      (is= (s-of-m (infer {} expr11)) "(c -> d) -> (d -> e) -> c -> e"))))
