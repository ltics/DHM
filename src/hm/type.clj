(ns hm.type
  (require [adt.sweet :refer :all]))

;; tvname → type variable name

(defadt ::prim
  PInt
  PBool
  PString)

(defadt ::mono
  (TVar tvname)
  (TPrm prim)
  (TFun lmono rmono)
  ;; support multiple args
  (TArrow monos mono)
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
                  PBool "bool"
                  PString "string")
    (TVar name) (s-of-tvn name)
    (TFun lmono rmono) (match lmono
                         (TFun _) (match rmono
                                    (TFun _) (format "(%s) → (%s)"
                                                     (s-of-m lmono)
                                                     (s-of-m rmono))
                                    :else (format "(%s) → %s"
                                                  (s-of-m lmono)
                                                  (s-of-m rmono)))
                         :else (match rmono
                                 (TFun _) (format "%s → (%s)"
                                                  (s-of-m lmono)
                                                  (s-of-m rmono))
                                 :else (format "%s → %s"
                                               (s-of-m lmono)
                                               (s-of-m rmono))))
    (TArrow monos mono) (if (= (count monos) 1)
                          (let [param-mono (first monos)]
                            (match param-mono
                              (TArrow _) (format "(%s) → %s"
                                                 (s-of-m param-mono)
                                                 (s-of-m mono))
                              :else (format "%s → %s"
                                            (s-of-m param-mono)
                                            (s-of-m mono))))
                          (format "(%s) → %s"
                                  (->> monos
                                       (map s-of-m)
                                       (clojure.string/join ", "))
                                  (s-of-m mono)))
    (TList mono) (format "[%s]" (s-of-m mono))
    (TPair lmono rmono) (format "(%s * %s)"
                                (s-of-m lmono)
                                (s-of-m rmono))
    (TError msg) msg))

(defn s-of-t
  "string of types"
  [t]
  (match t
    (Poly vnames mono) (if (empty? vnames)
                         (s-of-m mono)
                         (format "∀%s. %s"
                                 (->> vnames
                                      (map s-of-tvn)
                                      (clojure.string/join ","))
                                 (s-of-m mono)))
    :else (s-of-m t)))
