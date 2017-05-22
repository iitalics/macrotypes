#lang s-exp "../linear.rkt"

; basics
(check-linear 4)
(check-linear (λ ([b : Int]) 3))
(check-linear (λ ([b : (Box Int)]) b))
(check-linear (λ ([b : (Box Int)]) ())
              #:fail "b: linear variable may be unused")

; branching
(check-linear (λ ([x : Bool])
                (let ([b (box 3)])
                  (if x b b))))

(check-linear (λ ([x : Bool])
                (let ([b (box 3)])
                  (if x b (box 0))))
              #:fail "b: linear variable may be unused")

(check-linear (λ ([x : Bool])
                (let ([b (box 3)])
                  (if x b
                      (begin b (box 0))))))

; overusage
(check-linear (λ ([b : (Box Int)])
                (tup b b))
              #:fail "b: linear variable may be used more than once")

; unrestricted lambda
(check-linear (λ ([b : (Box Int)])
                (λ () b))
              #:fail "b: linear variable may be unused")

(check-linear (λ ([b : (Box Int)])
                (begin b (λ () b)))
              #:fail "b: linear variable may be used more than once")

; linear lambda
(check-linear (λ ([b : (Box Int)])
                (λ once () b)))

; application
(check-linear (λ ([f : (-> Int Int)]) (f 3)))
(check-linear (λ ([f : (-> Int Int)]) (tup (f 3) (f 4))))
(check-linear (λ ([f : (-o Int Int)]) (f 3)))
(check-linear (λ ([f : (-o Int Int)]) (tup (f 3) (f 4)))
              #:fail "f: linear variable may be used more than once")

; tuple types (linear only if any subtypes are linear)
(check-linear (lambda ([p : (× Int Int)]) ()))
(check-linear (lambda ([p : (× Int (Box Int))]) ())
              #:fail "p: linear variable may be unused")


; typing checks
(check-type 3 : Int)
(check-type #f : Bool)
(check-type () : Unit)
(check-type (tup 1 ()) : (× Int Unit))
(check-type (lambda ([x : Int]) x) : (-> Int Int))
(check-type (lambda ([x : (Box Int)]) x) : (-> (Box Int) (Box Int)))
(check-type (lambda once ([x : Int]) ()) : (-o Int Unit))
(check-type (if #t 3 4) : Int)
(check-type (if 4 3 4) #:fail)
