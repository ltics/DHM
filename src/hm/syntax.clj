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
