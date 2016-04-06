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
  (ELetRec vname expr body))

;; types

(defadt ::prim
  PInt
  PBool)

(defadt ::mono
  (TVar tvname)
  (TPrm prim)
  (TFun lmono rmono)
  (TError msg))

(defadt ::poly
  (Mono mono)
  (Poly tvnames mono))

(defn ftv
  "return the set of free type variable names"
  [t]
  (match t
    (Mono mono) (match mono
                  (TVar tvname) #{tvname}
                  (TFun lmono rmono) (clojure.set/union (ftv (Mono lmono))
                                                        (ftv (Mono rmono)))
                  :else #{})
    (Poly tvnames mono) (clojure.set/difference (ftv (Mono mono)) tvnames)))

(defn s-of-tvn
  "string of type variable names"
  [x]
  (if (and (>= x 0) (< x 26))
    (->> x (+ 97) char str)
    (if (and (>= x 26) (< x 52))
      (->> x (+ 39) char str)
      (format "τ%d" x))))

(defn s-of-m
  "string of monotypes"
  [t]
  (match t
    (TPrm prim) (match prim
                  PInt "int"
                  PBool "bool")
    (TVar name) (s-of-tvn name)
    (TFun lmono rmono) (match lmono
                         (TFun _) (format "(%s) -> %s"
                                          (s-of-m lmono)
                                          (s-of-m rmono))
                         :else (format "%s -> %s"
                                       (s-of-m lmono)
                                       (s-of-m rmono)))
    (TError msg) msg))

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
                            (s-of-expr b))))

(defn s-of-paren-expr
  "expr surround with parenthesis"
  [e]
  (match e
    (EAbs _) (format "(%s)" (s-of-expr e))
    (EApp _) (format "(%s)" (s-of-expr e))
    (ELet _) (format "(%s)" (s-of-expr e))
    (ELetRec _) (format "(%s)" (s-of-expr e))
    :else (s-of-expr e)))
