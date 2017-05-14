#lang s-exp "../../contexty/dunf-krishn-lang.rkt"
(require "../rackunit-typechecking.rkt")

(check-type 4 : Nat)
(check-type 4 : Int)
(check-type 4 : Num)
(check-type -4 : Int)
(check-type -4 : Num)
(check-type 4.1 : Num)
(check-not-type 4 : Unit)

(check-type (λ (x) x) : (→ Int Int))
(check-type (λ (x) x) : (→ Int Num))
(check-not-type (λ (x) x) : (→ Int Nat))

(check-type (suc 2) : Nat -> 3)
(check-type (inc 2) : Int -> 3)
(check-not-type (inc 2) : Nat)

(check-type (lambda (x) (inc x)) : (→ Int Int))
(check-not-type (lambda (x) (inc x)) : (→ Nat Nat))

(typecheck-fail (1 2) #:with-msg "application: not a function type: Nat")
