(ns hm.syntax
  (require [adt.sweet :refer :all]))

;; vname -> varaible name
;; tvname -> type variable name

;; values

(defadt ::lit
  (LInt value)
  (LBool value))

(defadt ::expr
  (EVar vname)
  (ELit lit)
  (EAbs vname expr)
  (EApp lexpr rexpr)
  (ELet vname expr body)
  (ELetRec vname expr body)
  ;; extra terms for algs
  (ESucc num)
  (EPred num)
  (ETimes lnum rnum)
  (EIsZero num)
  (EIf pred consequent alternative)
  (EFix abs)
  ENil
  (ECons e l)
  (EHead list)
  (ETail list)
  (EIsEmpty list)
  (EPair lexpr rexpr))

;; types

(defadt ::prim
  PInt
  PBool)

(defadt ::mono
  (TVar tvname)
  (TPrm prim)
  (TFun lmono rmono)
  (TList mono)
  (TPair lmono rmono)
  (TError msg))

(defadt ::poly
  (Mono mono)
  (Poly tvnames mono))

(def fresh-state (atom 0))

(defn pick-fresh-tvname
  "pick up a unique type variable name"
  []
  (swap! fresh-state inc)
  (dec @fresh-state))

(defn s-of-tvn
  "string of type variable names"
  [x]
  (cond
    (integer? x) (if (and (>= x 0) (< x 26))
                   (->> x (+ 97) char str)
                   (if (and (>= x 26) (< x 52))
                     (->> x (+ 39) char str)
                     (format "τ%d" (- x 52))))
    (string? x) (s-of-tvn (pick-fresh-tvname))
    :else (throw (Exception. "invalid type variable name"))))

(defn s-of-m
  "string of monotypes"
  [t]
  (match t
    (TPrm prim) (match prim
                  PInt "int"
                  PBool "bool")
    (TVar name) (s-of-tvn name)
    (TFun lmono rmono) (match lmono
                         (TFun _) (match rmono
                                    (TFun _) (format "(%s) -> (%s)"
                                                     (s-of-m lmono)
                                                     (s-of-m rmono))
                                    :else (format "(%s) -> %s"
                                                  (s-of-m lmono)
                                                  (s-of-m rmono)))
                         :else (match rmono
                                 (TFun _) (format "%s -> (%s)"
                                                  (s-of-m lmono)
                                                  (s-of-m rmono))
                                 :else (format "%s -> %s"
                                               (s-of-m lmono)
                                               (s-of-m rmono))))
    (TList mono) (format "[%s]" (s-of-m mono))
    (TPair lmono rmono) (format "(%s * %s)"
                                (s-of-m lmono)
                                (s-of-m rmono))
    (TError msg) msg))

(defn s-of-t
  "string of types"
  [t]
  (match t
    (Poly vnames mono) (format "∀%s. %s"
                               (clojure.string/join "" vnames)
                               (s-of-m mono))
    :else (s-of-m t)))

(declare s-of-paren-expr)

(defn s-of-expr
  "string of expression"
  [e]
  (match e
    (EVar name) name
    (ELit lit) (match lit
                 (LInt i) i
                 (LBool b) (if b "true" "false"))
    (EAbs n e) (format "λ%s -> %s" n (s-of-expr e))
    (EApp le re) (format "%s %s"
                         (s-of-expr le)
                         (s-of-paren-expr re))
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
    (EIsZero num) (format "zero? %s" (s-of-expr num))
    (EIf p c a) (format "if %s then %s else %s"
                        (s-of-expr p)
                        (s-of-expr c)
                        (s-of-expr a))
    (EFix abs) (format "fix(%s)" (s-of-expr abs))
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
