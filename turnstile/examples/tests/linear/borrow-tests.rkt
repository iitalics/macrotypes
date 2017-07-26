#lang s-exp turnstile/examples/linear/borrow
(require turnstile/rackunit-typechecking)

(check-type (tup 1 2) : (⊗ Int Int))

(typecheck-fail (let ([x (tup 1 2)])
                  (with-ptr p @ x
                    x))
                #:with-msg "x: variable cannot be used while borrowed\n  borrowed by: p")

(check-type (let ([x (tup 1 2)])
              (let ([y (with-ptr p @ x
                         (deref (fst p)))])
                (drop x)
                y))
            : Int ⇒ 1)

(typecheck-fail (let ([x (tup 1 2)])
                  (with-ptr p @ x
                    (deref p)))
                #:with-msg "can only deref unrestricted types, given \\(⊗ Int Int\\)")
