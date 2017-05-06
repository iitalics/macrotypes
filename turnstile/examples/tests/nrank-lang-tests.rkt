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
(check-type (λ (x) x) : (→ Num Num))
(check-type (λ (x) x) : (→ Nat Num))
(check-type (λ (x) (λ (y) x)) : (→ Unit (→ Num Unit)))
(typecheck-fail (ann (λ (x) (λ (y) x)) : (→ Unit (→ Num Num))))

; foralls
; (cannot directly check because typechecking needs to
;  go through the (tycheck ..) function to work properly)
(check-type (ann (λ (x) x) : (All (A) (→ A A)))
            : (All (A) (→ A A)))

; rank-2 foralls
(check-type (λ (f) (f 3)) : (→ (All (X) (→ X X)) Nat))

; definitions
(define x : Int 3)
(check-type x : Int)

(define-type-alias Bool (All (X) (→ X (→ X X))))
(define if : (All (X) (→ Bool (→ X (→ X X))))
  (lambda (f x y) (f x y)))
(define tru : Bool (lambda (x y) x))
(define fal : Bool (lambda (x y) y))

(check-type (if tru 4 5) : Int ⇒ 4)
(check-type (if tru () ()) : Unit)
(typecheck-fail (if () 4 5))
