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
    (let [fun-id    (EAbs "x" (EVar "x"))
          fun-true  (EAbs "x" (EAbs "y" (EVar "x")))
          fun-false (EAbs "x" (EAbs "y" (EVar "y")))
          e-true    (ELit (LBool true))
          e-false   (ELit (LBool false))
          e-1       (ELit (LInt 1))
          e-2       (ELit (LInt 2))
          expr0     (ELet "x" fun-id (EApp (EApp fun-false (EVar "x"))
                                           (EApp (EApp (EVar "x") (EVar "x")) e-false)))
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
          ;; λf → λg → λarg → g (f arg)
          expr11    (EAbs "f"
                          (EAbs "g"
                                (EAbs "arg"
                                      (EApp (EVar "g")
                                            (EApp (EVar "f") (EVar "arg"))))))
          expr12    (EApp (EVar "id")
                          (EApp (EVar "id")
                                (ELit (LInt 3))))
          expr13    (EApp (EApp (EVar "compose")
                                (EVar "not"))
                          (EApp (EVar "eq")
                                (ELit (LInt 3))))
          expr14    (EApp (EApp (EVar "add")
                                (ELit (LBool true)))
                          (ELit (LBool false)))
          ;; compose1 (b → c) → ((a → b) → (a → c))
          ;; compose2 (e → f) → ((d → e) → (d → f))
          ;; just substitution game
          expr15    (EApp (EVar "compose")
                          (EVar "compose"))
          expr16    (EApp (EApp (EVar "and")
                                (ELit (LBool true)))
                          (ELit (LBool false)))]
      (is= (s-of-t (infer {} fun-id))
           "a → a")
      (is= (s-of-t (infer {} fun-true))
           "a → (b → a)")
      (is= (s-of-t (infer {} fun-false))
           "a → (b → b)")
      (is= (s-of-t (infer {} e-true))
           (s-of-t (infer {} e-false))
           "bool")
      (is= (s-of-t (infer {} e-1))
           (s-of-t (infer {} e-2))
           "int")
      (is= (s-of-t (infer {} expr0)) "bool")
      (is= (s-of-t (infer {} expr1)) "b → b")
      (is= (s-of-t (infer {} expr2)) "c → c")
      (is= (s-of-t (infer {} expr3)) "c → c")
      (is= (s-of-t (infer {} expr4)) "int")
      (is= (s-of-t (infer {} expr5)) "occurs check fails: a vs. a → b in x x")
      (is= (s-of-t (infer {} expr6)) "(bool → b) → b")
      (is= (s-of-t (infer {} expr7)) "types do not unify: int vs. int → a in 3 3")
      (is= (s-of-t (infer {} expr8)) "(int → h) → h")
      (is= (s-of-t (infer {} expr9)) "occurs check fails: d vs. d → e in b (a (a b))")
      (is= (s-of-t (infer {} expr10)) "int")
      (is= (s-of-t (infer {} expr11)) "(c → d) → ((d → e) → (c → e))")
      (is= (s-of-t (infer assumptions expr12)) "int")
      (is= (s-of-t (infer assumptions expr13)) "int → bool")
      (is= (s-of-t (infer assumptions expr14)) "types do not unify: int vs. bool in add true")
      (is= (s-of-t (infer assumptions expr15)) "(a → (e → f)) → (a → ((d → e) → (d → f)))")
      (is= (s-of-t (infer assumptions expr16)) "bool")))
  ;; generally saying TFun is also a compound type
  (testing "inference compound types"
    (let [expr0  (EApp (EApp (EVar "pair")
                             (ELit (LInt 3)))
                       (ELit (LInt 3)))
          expr1  (EApp (EApp (EVar "pair")
                             (EApp (EVar "f") (ELit (LInt 3))))
                       (EApp (EVar "f") (ELit (LInt 3))))
          expr2  (EAbs "f"
                       (EApp (EApp (EVar "pair")
                                   (EApp (EVar "f") (ELit (LInt 3))))
                             (EApp (EVar "f") (ELit (LInt 3)))))
          expr3  (EAbs "f"
                       (EApp (EApp (EVar "pair")
                                   (EApp (EVar "f") (ELit (LInt 3))))
                             (EApp (EVar "f") (ELit (LBool true)))))
          expr4  (ELet "f"
                       (EAbs "x" (EVar "x"))
                       (EApp (EApp (EVar "pair")
                                   (EApp (EVar "f") (ELit (LInt 3))))
                             (EApp (EVar "f") (ELit (LBool true)))))
          expr5  (EAbs "g"
                       (ELet "f"
                             (EAbs "x" (EVar "g"))
                             (EApp (EApp (EVar "pair")
                                         (EApp (EVar "f") (ELit (LInt 3))))
                                   (EApp (EVar "f") (ELit (LBool true))))))
          ;; let rec len = λxs → if (isempty xs) 0 (succ (len (tail xs))) in len (cons 0 nil)
          expr6  (ELetRec "len"
                          (EAbs "xs"
                                (EApp (EApp (EApp (EVar "if")
                                                  (EApp (EVar "isempty") (EVar "xs")))
                                            (ELit (LInt 0)))
                                      (EApp (EVar "succ")
                                            (EApp (EVar "len")
                                                  (EApp (EVar "tail") (EVar "xs"))))))
                          (EApp (EVar "len")
                                (EApp (EApp (EVar "cons")
                                            (ELit (LInt 0)))
                                      (EVar "nil"))))
          expr7  (ELetRec "len"
                          (EAbs "xs"
                                (EApp (EApp (EApp (EVar "if")
                                                  (EApp (EVar "isempty") (EVar "xs")))
                                            (ELit (LInt 0)))
                                      (EApp (EVar "succ")
                                            (EApp (EVar "len")
                                                  (EApp (EVar "tail") (EVar "xs"))))))
                          (EVar "len"))
          ;; let-polymorphism, prenex polymorphism or more generally rank-1 polymorphism
          expr8  (ELet "f"
                       (EAbs "x" (EVar "x"))
                       (ELet "p"
                             (EApp (EApp (EVar "pair")
                                         (EApp (EVar "f") (ELit (LInt 3))))
                                   (EApp (EVar "f") (ELit (LBool true))))
                             (EVar "p")))
          ;; not allow polymorphic lambda abstraction
          expr9  (EAbs "id"
                       (EApp (EApp (EVar "pair")
                                   (EApp (EVar "id")
                                         (ELit (LBool true))))
                             (EApp (EVar "id")
                                   (ELit (LInt 3)))))
          expr10 (EApp (EApp (EVar "pair")
                             (ELit (LString "term")))
                       (ELit (LInt 3)))]
      (is= (s-of-t (infer assumptions expr0)) "(int * int)")
      (is= (s-of-t (infer assumptions expr1)) "unbound variable: f")
      (is= (s-of-t (infer assumptions expr2)) "(int → f) → (f * f)")
      (is= (s-of-t (infer assumptions expr3)) "types do not unify: int vs. bool in f true")
      (is= (s-of-t (infer assumptions expr4)) "(int * bool)")
      (is= (s-of-t (infer assumptions expr5)) "i → (i * i)")
      (is= (s-of-t (infer assumptions expr6)) "int")
      (is= (s-of-t (infer assumptions expr7)) "[d] → int")
      (is= (s-of-t (infer assumptions expr8)) "(int * bool)")
      (is= (s-of-t (infer assumptions expr9)) "types do not unify: bool vs. int in id 3")
      (is= (s-of-t (infer assumptions expr10)) "(string * int)")))
  (testing "inference recursive function types"
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
                         (EApp (EVar "factorial") (ELit (LInt 5))))
          ;; letrec is just a suger of let and fix point combinator
          expr2 (ELet "factorial"
                      (EApp (EVar "fix")
                            (EAbs "factorial"
                                  (EAbs "n"
                                        (EApp (EApp (EApp (EVar "if")
                                                          (EApp (EVar "iszero")
                                                                (EVar "n")))
                                                    (ELit (LInt 1)))
                                              (EApp (EApp (EVar "times")
                                                          (EVar "n"))
                                                    (EApp (EVar "factorial")
                                                          (EApp (EVar "pred")
                                                                (EVar "n"))))))))
                      (EVar "factorial"))
          expr3 (ELet "factorial"
                      (EApp (EVar "fix")
                            (EAbs "factorial"
                                  (EAbs "n"
                                        (EApp (EApp (EApp (EVar "if")
                                                          (EApp (EVar "iszero")
                                                                (EVar "n")))
                                                    (ELit (LInt 1)))
                                              (EApp (EApp (EVar "times")
                                                          (EVar "n"))
                                                    (EApp (EVar "factorial")
                                                          (EApp (EVar "pred")
                                                                (EVar "n"))))))))
                      (EApp (EVar "factorial") (ELit (LInt 5))))]
      (is= (s-of-t (infer assumptions expr0)) "int → int")
      (is= (s-of-t (infer assumptions expr1)) "int")
      (is= (s-of-t (infer assumptions expr2)) "int → int")
      (is= (s-of-t (infer assumptions expr3)) "int"))))
