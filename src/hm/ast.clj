(ns hm.ast
  (require [adt.sweet :refer :all]))

;; vname → varaible name

(defadt ::lit
  (LInt value)
  (LBool value)
  (LString value))

(defadt ::expr
  (EVar vname)
  (ELit lit)
  (EAbs vname expr)
  (EApp lexpr rexpr)
  ;; support multiple args
  (EFun vnames expr)
  (ECall expr exprs)
  (ELet vname expr body)
  (ELetRec vname expr body)
  ;; extra terms for algs
  (ESucc num)
  (EPred num)
  (ETimes lnum rnum)
  (EAdd lnum rnum)
  (EIsZero num)
  (EIf pred consequent alternative)
  (EFix abs)
  (EId expr)
  (ENot bool)
  (EAnd lbool rbool)
  (EEq lexpr rexpr)
  (ECompose lfun rfun)
  ENil
  (ECons e l)
  (EHead list)
  (ETail list)
  (EIsEmpty list)
  (EPair lexpr rexpr))

(declare s-of-paren-expr)

(defn s-of-expr
  "string of expression"
  [e]
  (match e
    (EVar name) name
    (ELit lit) (match lit
                 (LInt i) i
                 (LBool b) (if b "true" "false")
                 (LString s) (format "\"%s\"" s))
    (EAbs n e) (format "λ%s → %s" n (s-of-expr e))
    (EFun ns e) (format "ƒ %s → %s"
                        (clojure.string/join " " ns)
                        (s-of-expr e))
    (EApp le re) (format "%s %s"
                         (s-of-expr le)
                         (s-of-paren-expr re))
    (ECall f args) (format "%s(%s)"
                           (s-of-expr f)
                           (->> args
                                (map s-of-expr)
                                (clojure.string/join ", ")))
    (ELet n e b) (format "let %s = %s in %s"
                         n
                         (s-of-expr e)
                         (s-of-expr b))
    (ELetRec n e b) (format "let rec %s = %s in %s"
                            n
                            (s-of-expr e)
                            (s-of-expr b))
    (ESucc num) (format "succ %s" (s-of-expr num))
    (EPred num) (format "pred %s" (s-of-expr num))
    (ETimes lnum rnum) (format "%s * %s"
                               (s-of-expr lnum)
                               (s-of-expr rnum))
    (EAdd lnum rnum) (format "%s + %s"
                             (s-of-expr lnum)
                             (s-of-expr rnum))
    (EIsZero num) (format "zero? %s" (s-of-expr num))
    (EIf p c a) (format "if %s then %s else %s"
                        (s-of-expr p)
                        (s-of-expr c)
                        (s-of-expr a))
    (EFix abs) (format "fix(%s)" (s-of-expr abs))
    (EId expr) (format "id(%s)" (s-of-expr expr))
    (ENot bool) (format "¬ %s" (s-of-expr bool))
    (EAnd lbool rbool) (format "%s ∧ %s"
                               (s-of-expr lbool)
                               (s-of-expr rbool))
    (EEq lexpr rexpr) (format "%s ≡ %s"
                              (s-of-expr lexpr)
                              (s-of-expr rexpr))
    (ECompose lfun rfun) (format "%s ∘ %s"
                                 (s-of-expr lfun)
                                 (s-of-expr rfun))
    ENil "[]"
    (ECons e l) (format "%s :: %s"
                        (s-of-expr e)
                        (s-of-expr l))
    (EHead l) (format "head %s" (s-of-expr l))
    (ETail l) (format "tail %s" (s-of-expr l))
    (EIsEmpty l) (format "empty? %s" (s-of-expr l))
    (EPair lexpr rexpr) (format "(%s, %s)"
                                (s-of-expr lexpr)
                                (s-of-expr rexpr))))

(defn s-of-paren-expr
  "expr surround with parenthesis"
  [e]
  (match e
    (EAbs _) (format "(%s)" (s-of-expr e))
    (EApp _) (format "(%s)" (s-of-expr e))
    (ELet _) (format "(%s)" (s-of-expr e))
    (ELetRec _) (format "(%s)" (s-of-expr e))
    :else (s-of-expr e)))
