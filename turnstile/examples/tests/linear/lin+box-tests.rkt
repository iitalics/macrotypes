#lang s-exp turnstile/examples/linear/lin+box
(require turnstile/rackunit-typechecking)

(check-type (box) : Box0)
(check-type (box 3) : (Box Int))
(check-type (unbox (box 3)) : (⊗ Box0 Int))

(check-type
 (let* ([b1 (box 3)]
        [(l1 x) (unbox b1)]
        [b2 (box 4 @ l1)]
        [(l2 y) (unbox b2)])
   (drop l2)
   (+ x y))
 : Int ⇒ 7)

(typecheck-fail
 (let* ([l (box)]
        [f (λ ! ([z : String])
              (box z @ l))])
   (tup (f "a") (f "b")))
 #:with-msg "linear variable may not be used by unrestricted function")
