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
  (ELet vname expr body))

;; types

(defadt ::prim
  PInt
  PBool)

(defadt ::mono
  (TVar tvname)
  (TPrm prim)
  (TFun lmono rmono)
  TError)

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
      (format "(%d)" x))))

(defn s-of-m
  "string of monotypes"
  [t]
  (match t
    (TPrm prim) (match prim
                  PInt "int"
                  PBool "bool")
    (TVar name) (s-of-tvn name)
    (TFun lmono rmono) (format "(%s -> %s)"
                               (s-of-m lmono)
                               (s-of-m rmono))
    TError "ERROR"))
