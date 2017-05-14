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
