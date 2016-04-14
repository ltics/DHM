(ns hm.error
  (require [hm.ast :refer :all]
           [hm.type :refer :all]))

(defn throw-occurs-exp
  [m1 m2]
  (throw (Exception. (format "occurs check fails: %s vs. %s"
                             (s-of-m m1)
                             (s-of-m m2)))))

(defn throw-unify-exp
  [m1 m2]
  (throw (Exception. (format "types do not unify: %s vs. %s"
                             (s-of-m m1)
                             (s-of-m m2)))))

(defn throw-unbound-exp
  [n]
  (throw (Exception. (format "unbound variable: %s" n))))

(defn throw-innerexpr-exp
  [e expr]
  (throw (Exception. (format "%s in %s"
                             (.getMessage e)
                             (s-of-expr expr)))))

(defn throw-unknown-exp
  [expr]
  (throw (Exception. (format "unknown type for give expression: %s"
                             (s-of-expr expr)))))

(defn throw-expected-func-exp
  [expr]
  (throw (Exception. (format "expected a function: %s"
                             (s-of-expr expr)))))

(defn throw-unexpected-number-args-exp
  [expr]
  (throw (Exception. (format "unexpected number of arguments: %s"
                             (s-of-expr expr)))))
