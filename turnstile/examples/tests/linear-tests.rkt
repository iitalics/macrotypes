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
(check-linear (λ ([p : (× Int Int)]) ()))
(check-linear (λ ([p : (× Int (Box Int))]) ())
              #:fail "p: linear variable may be unused")


; typing checks
(check-type 3 : Int)
(check-type #f : Bool)
(check-type () : Unit)
(check-type (tup 1 ()) : (× Int Unit))
(check-type (λ ([x : Int]) x) : (-> Int Int))
(check-type (λ ([x : (Box Int)]) x) : (-> (Box Int) (Box Int)))
(check-type (λ once ([x : Int]) ()) : (-o Int Unit))
(check-type (if #t 3 4) : Int)
(check-type (if 4 3 4) #:fail)


; standard functions test
(check-type + : (-> Int Int Int))
(check-type (+ 1 2) : Int)
(check-type (λ ([b : (Box Int)])
              (let ([v (take-int b)])
                (if (< 10 v)
                    (box 0)
                    (box (+ 1 v)))))
            : (-> (Box Int) (Box Int)))
