#lang s-exp "../nrank.rkt"
(require "rackunit-typechecking.rkt")

; datum
(check-type () : Unit)
(check-type 4 : Nat)
(check-type 4 : Int)
(check-type 4 : Num)
(check-type -1 : Int)
(check-type -1 : Num)
(check-type 3.5 : Num)

; simple application
(check-type succ : (→ Nat Nat))
(check-type (succ 1) : Nat)
(typecheck-fail (succ 1.0))

; instantiated
(check-type id : (All (X) (→ X X)))
(check-type (id 3) : Nat)
(check-type (id 3) : Int)
(check-type (id 3) : Num)

; lambdas
(check-type (lambda (x) x) : (→ Num Num))
(check-type (lambda (x) x) : (→ Nat Num))
(check-type (lambda (x) (lambda (y) x)) : (→ Unit (→ Num Unit)))
(typecheck-fail (ann (lambda (x) (lambda (y) x)) : (→ Unit (→ Num Num))))

; foralls
; (cannot directly check because typechecking needs to
;  go through the (tycheck ..) function to work properly)
(check-type (ann (lambda (x) x) : (All (A) (→ A A)))
            : (All (A) (→ A A)))

; rank-2 foralls
(check-type (lambda (f) (f 3)) : (→ (All (X) (→ X X)) Nat))
