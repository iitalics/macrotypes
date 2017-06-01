#lang s-exp "../linear-mixed/mixed.rkt"
(require "../../rackunit-typechecking.rkt")

;; basic types, and linear interop

(check-type 1 : Int)
(check-type #t : Bool)
(check-type "a" : Str)
(check-type () : Unit)

(check-type (UL 1) : Int)
(check-type (UL #t) : Bool)
(check-type (UL ()) : Unit)

(check-type (tup 1 2) : (× Int Int))
(check-type (UL/test (tup 1 2)) : (⊗ Int Int))
(check-type (UL (tup 1 2)) : (× Int Int))

(check-type (tup 1 (tup 2 3)) : (× Int (× Int Int)))
(check-type (UL/test (tup 1 (tup 2 3))) : (⊗ Int (⊗ Int Int)))
(check-type (UL (tup 1 (tup 2 3))) : (× Int (× Int Int)))

(check-type (lambda ([x : Int]) x) : (-> Int Int))
(check-type (UL/test (lambda ([x : Int]) x)) : (-o Int Int))
(check-type (UL (lambda ([x : Int]) x)) : (-> Int Int))

(check-type (UL/test (lambda ([x : (Box Int)]) x)) : (-o (Box Int) (Box Int)))
(typecheck-fail (UL (lambda ([x : (Box Int)]) x))
                #:with-msg "linear type .+ cannot escape linear context")


;; tuple destructuring

(check-type (let* ([p (tup 1 4)] [(x y) p]) x)
            : Int -> 1)

(check-type (UL (let* ([p (tup 1 2 3 4 5)]
                       [(x y z t s) p])
                  t))
            : Int -> 4)

(typecheck-fail (UL (let* ([p (tup 1 2 3 4 5)]
                           [(x y z t) p])
                      t))
                #:with-msg "wrong number of elements in tuple")

(typecheck-fail (let* ([p (tup 1 2 3 4 5)]
                       [(x y z t) p])
                  t)
                #:with-msg "wrong number of elements in tuple")



;; linear mechanics

(check-type (UL (let ([x (tup 1 #t)])
                  x))
            : (× Int Bool))

(typecheck-fail (UL (let ([x (tup 1 #t)])
                      0))
                #:with-msg "x: linear variable unused")

(typecheck-fail (UL (let ([x (tup 1 #t)])
                      (begin x x)))
                #:with-msg "x: linear variable used more than once")

(typecheck-fail (UL (let ([y (tup #f #f)])
                      (if #t
                          y
                          (tup #t #t))))
                #:with-msg "y: linear variable may be unused")



;; sharing

(check-type (UL (let ([x (share (tup 2 ()))])
                  x))
            : (× Int Unit))

(check-type (UL/test (let ([x (share (tup 2 ()))])
                       (tup (copy x) (copy x))))
            : (⊗ (⊗ Int Unit) (⊗ Int Unit)))

(check-type (UL/test (let ([x (share (tup 2 ()))])
                       (tup x x)))
            : (⊗ (!! (⊗ Int Unit))
                 (!! (⊗ Int Unit))))

(check-type (UL (let ([x (share (tup 4 #f))])
                  (tup x x)))
            : (× (× Int Bool) (× Int Bool))
            -> (tup (tup 4 #f) (tup 4 #f)))

(typecheck-fail (UL (let ([x (tup #t #t)])
                      (share x)))
                #:with-msg "x: may not share linear variable")

(check-type (UL (let* ([b (share (box 3))]
                       [(l1 x1) (unbox (copy b))]
                       [b2 (box l1 4)]
                       [(l2 x2) (unbox (copy b))])
                  (begin b2 l2 x2)))
            : Int -> 3)



;; standard lib

(check-type (UL (let ([zero? (share (lambda ([x : Int])
                                      (if (< x 0) #f
                                          (if (< 0 x) #f
                                              #t))))])
                  (tup (zero? 2)
                       (zero? 0)
                       (zero? -2))))
            : (× Bool Bool Bool)
            -> (tup #f #t #f))

(check-type (UL (let* ([b (box 3)]
                       [(loc x) (unbox (inc (inc (inc b))))])
                  (begin loc x)))
            : Int -> 6)
