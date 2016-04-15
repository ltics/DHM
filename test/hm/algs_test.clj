(ns hm.algs-test
  (require [acolfut.sweet :refer :all]
           [hm.ast :refer :all]
           [hm.type :refer :all]
           [hm.env :refer :all]
           [hm.algs :refer :all]
           [hm.normalize :refer :all]))

(deftest algs-test
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
          expr12    (EId (EId (ELit (LInt 3))))
          expr13    (ECompose (EAbs "x" (ENot (EVar "x")))
                              (EAbs "x" (EEq (ELit (LInt 3)) (EVar "x"))))
          expr14    (EAdd (ELit (LBool true))
                          (ELit (LBool false)))
          ;; compose1 (b → c) → ((a → b) → (a → c))
          ;; compose2 (e → f) → ((d → e) → (d → f))
          ;; just substitution game
          expr15    (EAbs "x"
                          (ECompose (EAbs "y"
                                          (EAbs "z"
                                                (ECompose (EVar "y") (EVar "z"))))
                                    (EVar "x")))
          expr16    (EAnd (ELit (LBool true))
                          (ELit (LBool false)))
          expr17    (EApp (EApp (EVar "choose")
                                (EAbs "x"
                                      (EAbs "y"
                                            (EVar "x"))))
                          (EAbs "x"
                                (EAbs "y"
                                      (EVar "y"))))
          expr18    (ECall (EVar "choosea")
                           [(EFun ["a" "b"]
                                  (EVar "a"))
                            (EFun ["a" "b"]
                                  (EVar "b"))])
          expr19    (ECall (EVar "consa")
                           [(EVar "id")
                            (EVar "nil")])
          expr20    (EFun ["g" "y"]
                          (ECall (EVar "g")
                                 [(EVar "y")]))
          expr21    (EFun ["f"]
                          (ELet "x"
                                (EFun ["g" "y"]
                                      (ELet "_"
                                            (ECall (EVar "g")
                                                   [(EVar "y")])
                                            (ECall (EVar "eqa")
                                                   [(EVar "f")
                                                    (EVar "g")])))
                                (EVar "x")))
          expr22    (EApp (EApp (EVar "cons")
                                (EVar "id"))
                          (EApp (EApp (EVar "cons")
                                      (EVar "succ"))
                                (EApp (EApp (EVar "cons")
                                            (EVar "id"))
                                      (EVar "nil"))))
          expr23    (EFun ["x"]
                          (EFun ["y"]
                                (ELet "x"
                                      (ECall (EVar "x")
                                             [(EVar "y")])
                                      (EFun ["x"]
                                            (ECall (EVar "y")
                                                   [(EVar "x")])))))
          expr24    (ELet "lst1"
                          (EApp (EApp (EVar "cons")
                                      (EVar "id"))
                                (EVar "nil"))
                          (ELet "lst2"
                                (EApp (EApp (EVar "cons")
                                            (EVar "succ"))
                                      (EVar "lst1"))
                                (EVar "lst2")))
          expr25    (EFun ["x"]
                          (ELet "y"
                                (ELet "z"
                                      (ECall (EVar "x")
                                             [(EFun ["x"]
                                                    (EVar "x"))])
                                      (EVar "z"))
                                (EVar "y")))
          expr26    (ELet "apply"
                          (EFun ["f" "x"]
                                (ECall (EVar "f")
                                       [(EVar "x")]))
                          (EVar "apply"))
          expr27    (ELet "apply_curry"
                          (EFun ["f"]
                                (EFun ["x"]
                                      (ECall (EVar "f")
                                             [(EVar "x")])))
                          (EVar "apply_curry"))
          expr28    (ELet "apply_abs"
                          (EAbs "f"
                                (EAbs "x"
                                      (EApp (EVar "f")
                                            (EVar "x"))))
                          (EVar "apply_abs"))
          expr29    (ECall (EVar "applya")
                           [(EAbs "x"
                                  (EApp (EVar "succ")
                                        (EVar "x")))
                            (EVar "zero")])
          expr30    (ECall (EVar "applyaa")
                           [(EFun ["x"]
                                  (EApp (EVar "succ")
                                        (EVar "x")))
                            (EVar "zero")])
          expr31    (EFun ["y"] (EVar "y"))
          expr32    (EFun ["x"]
                          (EApp (EVar "x") (EVar "x")))
          expr33    (EAbs "x"
                          (EApp (EVar "x") (EVar "x")))
          expr34    (ECall (EVar "plus")
                           [(ELit (LInt 3))
                            (ELit (LBool true))])
          expr35    (ECall (EVar "plus")
                           [(ELit (LInt 3))])
          expr36    (ECall (EVar "zero")
                           [(ELit (LInt 3))])
          expr37    (EApp (EApp (EVar "const")
                                (EVar "zero"))
                          (EVar "true"))
          expr38    (EApp (EApp (EVar "apply")
                                (EAbs "x"
                                      (EApp (EVar "succ")
                                            (EVar "x"))))
                          (EVar "true"))
          expr39    (EApp (EApp (EVar "apply")
                                (EAbs "x"
                                      (EApp (EVar "succ")
                                            (EVar "x"))))
                          (EVar "zero"))
          expr40    (ECall (EVar "applya")
                           [(EAbs "x"
                                  (EApp (EVar "succ")
                                        (EVar "x")))
                            (EVar "true")])
          expr41    (EVar "id")
          expr42    (EVar "paira")]
      (is= (s-of-t (infer {} fun-id))
           "a → a")
      (is= (s-of-t (infer {} fun-true))
           "a → (b → a)")
      (is= (s-of-t (generalize {} (infer {} fun-true)))
           "∀a,b. a → (b → a)")
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
      (is= (s-of-t (infer {} expr5))
           "occurs check fails: a vs. a → b in let id = λx → x x in id")
      (is= (s-of-t (infer {} expr6)) "(bool → b) → b")
      (is= (s-of-t (infer {} expr7))
           "types do not unify: int vs. int → a in 3 3")
      (is= (s-of-t (infer {} expr8)) "(int → h) → h")
      (is= (s-of-t (infer {} expr9))
           "occurs check fails: d vs. d → e in λa → λb → b (a (a b))")
      (is= (s-of-t (infer {} expr10)) "int")
      (is= (s-of-t (infer {} expr11))
           "(c → d) → ((d → e) → (c → e))")
      (is= (s-of-t (infer assumptions expr12)) "int")
      (is= (s-of-t (infer assumptions expr13)) "int → bool")
      (is= (s-of-t (infer assumptions expr14)) "types do not unify: bool vs. int in true + false")
      (is= (s-of-t (infer assumptions expr15)) "(b → (h → i)) → (b → ((g → h) → (g → i)))")
      (is= (s-of-t (infer assumptions expr16)) "bool")
      (is= (s-of-t (generalize {} (infer assumptions expr17))) "∀a. a → (a → a)")
      (is= (s-of-t (generalize {} (infer assumptions expr18))) "∀a. (a, a) → a")
      (is= (s-of-t (generalize {} (infer assumptions expr19))) "∀a. [a → a]")
      (is= (s-of-t (generalize {} (infer assumptions expr20)))
           "∀a,b. (a → b, a) → b")
      (is= (s-of-t (generalize {} (infer assumptions expr21)))
           "∀a,b. (a → b) → (a → b, a) → bool")
      (is= (s-of-t (generalize {} (infer assumptions expr22))) "[int → int]")
      (is= (s-of-t (generalize {} (infer assumptions expr23))) "∀a,b,c. ((b → c) → a) → (b → c) → b → c")
      (is= (s-of-t (generalize {} (infer assumptions expr24))) "[int → int]")
      (is= (s-of-t (generalize {} (infer assumptions expr25))) "∀a,b. ((a → a) → b) → b")
      (is= (s-of-t (generalize {} (infer assumptions expr26))) "∀a,b. (a → b, a) → b")
      (is= (s-of-t (generalize {} (infer assumptions expr27))) "∀a,b. (a → b) → a → b")
      (is= (s-of-t (generalize {} (infer assumptions expr28))) "∀a,b. (a → b) → (a → b)")
      (is= (s-of-t (generalize {} (infer assumptions expr29))) "int")
      (is= (s-of-t (generalize {} (infer assumptions expr30))) "int")
      (is= (s-of-t (generalize {} (infer {} expr31))) "∀a. a → a")
      ;; recursive types a ~ a → b
      (is= (s-of-t (generalize {} (infer assumptions expr32)))
           "occurs check fails: a vs. a → b in ƒ x → x x")
      (is= (s-of-t (generalize {} (infer assumptions expr33)))
           "occurs check fails: a vs. a → b in λx → x x")
      (is= (s-of-t (generalize {} (infer assumptions expr34)))
           "types do not unify: int vs. bool in plus(3, true)")
      (is= (s-of-t (generalize {} (infer assumptions expr35)))
           "unexpected number of arguments: plus(3) in plus(3)")
      (is= (s-of-t (generalize {} (infer assumptions expr36)))
           "expected a function: zero in zero(3)")
      (is= (s-of-t (generalize {} (infer assumptions expr37)))
           "int")
      (is= (s-of-t (generalize {} (infer assumptions expr38)))
           "types do not unify: int vs. bool in apply (λx → succ x) true")
      (is= (s-of-t (generalize {} (infer assumptions expr39)))
           "int")
      (is= (s-of-t (generalize {} (infer assumptions expr40)))
           "types do not unify: bool vs. int in applya(λx → succ x, true)")
      (is= (s-of-t (generalize {} (infer assumptions expr41))) "∀a. a → a")
      (is= (s-of-t (generalize {} (infer assumptions expr42))) "∀a,b. (a, b) → (a * b)")))
  (testing "inference compound types"
    (let [expr0  (EPair (ELit (LInt 3))
                        (ELit (LBool true)))
          expr1  (EPair (EApp (EVar "f") (ELit (LInt 3)))
                        (EApp (EVar "f") (ELit (LInt 3))))
          expr2  (EAbs "f"
                       (EPair (EApp (EVar "f") (ELit (LInt 3)))
                              (EApp (EVar "f") (ELit (LInt 3)))))
          expr3  (EAbs "f"
                       (EPair (EApp (EVar "f") (ELit (LInt 3)))
                              (EApp (EVar "f") (ELit (LBool true)))))
          expr4  (ELet "f"
                       (EAbs "x" (EVar "x"))
                       (EPair (EApp (EVar "f") (ELit (LInt 3)))
                              (EApp (EVar "f") (ELit (LBool true)))))
          expr5  (EAbs "g"
                       (ELet "f"
                             (EAbs "x" (EVar "g"))
                             (EPair (EApp (EVar "f") (ELit (LInt 3)))
                                    (EApp (EVar "f") (ELit (LBool true))))))
          ;; let rec len = λxs → if (isempty xs) 0 (succ (len (tail xs))) in len (cons 0 nil)
          expr6  (ELetRec "len"
                          (EAbs "xs"
                                (EIf (EIsEmpty (EVar "xs"))
                                     (ELit (LInt 0))
                                     (ESucc (EApp (EVar "len")
                                                  (ETail (EVar "xs"))))))
                          (EApp (EVar "len")
                                (ECons (ELit (LInt 0)) ENil)))
          expr7  (ELetRec "len"
                          (EAbs "xs"
                                (EIf (EIsEmpty (EVar "xs"))
                                     (ELit (LInt 0))
                                     (ESucc (EApp (EVar "len")
                                                  (ETail (EVar "xs"))))))
                          (EVar "len"))
          ;; let-polymorphism, prenex polymorphism or more generally rank-1 polymorphism
          expr8  (ELet "f"
                       (EAbs "x" (EVar "x"))
                       (ELet "p"
                             (EPair (EApp (EVar "f") (ELit (LInt 3)))
                                    (EApp (EVar "f") (ELit (LBool true))))
                             (EVar "p")))
          ;; not allow polymorphic lambda abstraction
          expr9  (EAbs "id"
                       (EPair (EApp (EVar "id") (ELit (LBool true)))
                              (EApp (EVar "id") (ELit (LInt 3)))))
          expr10 (EPair (ELit (LString "term"))
                        (ELit (LInt 3)))
          expr11 (ECons (EAbs "x" (EId (EVar "x")))
                        ENil)]
      (is= (s-of-t (infer assumptions expr0)) "(int * bool)")
      (is= (s-of-t (infer assumptions expr1)) "unbound variable: f in (f 3, f 3)")
      (is= (s-of-t (infer assumptions expr2)) "(int → c) → (c * c)")
      (is= (s-of-t (infer assumptions expr3)) "types do not unify: int vs. bool in λf → (f 3, f true)")
      (is= (s-of-t (infer assumptions expr4)) "(int * bool)")
      (is= (s-of-t (infer assumptions expr5)) "f → (f * f)")
      (is= (s-of-t (infer assumptions expr6)) "int")
      (is= (s-of-t (infer assumptions expr7)) "[e] → int")
      (is= (s-of-t (infer assumptions expr8)) "(int * bool)")
      (is= (s-of-t (infer assumptions expr9)) "types do not unify: bool vs. int in λid → (id true, id 3)")
      (is= (s-of-t (infer {} expr10)) "(string * int)")
      (is= (s-of-t (generalize {} (infer {} expr11))) "∀a. [a → a]")))
  (testing "inference recursive function types"
    (let [expr0 (ELetRec "factorial"
                         (EAbs "n"
                               (EIf (EIsZero (EVar "n"))
                                    (ELit (LInt 1))
                                    (ETimes (EVar "n")
                                            (EApp (EVar "factorial")
                                                  (EPred (EVar "n"))))))
                         (EVar "factorial"))
          expr1 (ELetRec "factorial"
                         (EAbs "n"
                               (EIf (EIsZero (EVar "n"))
                                    (ELit (LInt 1))
                                    (ETimes (EVar "n")
                                            (EApp (EVar "factorial")
                                                  (EPred (EVar "n"))))))
                         (EApp (EVar "factorial") (ELit (LInt 5))))
          ;; letrec is just a suger of let and fix point combinator
          expr2 (ELet "factorial"
                      (EFix (EAbs "factorial"
                                  (EAbs "n"
                                        (EIf (EIsZero (EVar "n"))
                                             (ELit (LInt 1))
                                             (ETimes (EVar "n")
                                                     (EApp (EVar "factorial")
                                                           (EPred (EVar "n"))))))))
                      (EVar "factorial"))
          expr3 (ELet "factorial"
                      (EFix (EAbs "factorial"
                                  (EAbs "n"
                                        (EIf (EIsZero (EVar "n"))
                                             (ELit (LInt 1))
                                             (ETimes (EVar "n")
                                                     (EApp (EVar "factorial")
                                                           (EPred (EVar "n"))))))))
                      (EApp (EVar "factorial") (ELit (LInt 5))))]
      (is= (s-of-t (infer assumptions expr0)) "int → int")
      (is= (s-of-t (infer assumptions expr1)) "int")
      (is= (s-of-t (infer assumptions expr2)) "int → int")
      (is= (s-of-t (infer assumptions expr3)) "int"))))
