#lang s-exp "../linear.rkt"


(check-linear 4)
(check-linear (λ ([b : Int]) 3))
(check-linear (λ ([b : (Box Int)]) b))
(check-linear (λ ([b : (Box Int)]) ())
              #:fail "b: linear variable may be unused")

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

(check-linear (λ ([b : (Box Int)])
                (tup b b))
              #:fail "b: linear variable may be used more than once")

(check-linear (λ ([b : (Box Int)])
                (λ () b))
              #:fail "b: linear variable may be unused")

(check-linear (λ ([b : (Box Int)])
                (begin b (λ () b)))
              #:fail "b: linear variable may be used more than once")

(check-linear (λ ([b : (Box Int)])
                (λ once () b)))

(check-linear (λ ([f : (-> Int Int)]) (f 3)))
(check-linear (λ ([f : (-> Int Int)]) (tup (f 3) (f 4))))
(check-linear (λ ([f : (-o Int Int)]) (f 3)))
(check-linear (λ ([f : (-o Int Int)]) (tup (f 3) (f 4)))
              #:fail "f: linear variable may be used more than once")


(check-type 3 : Int)
(check-type #f : Bool)
(check-type () : Unit)
(check-type (lambda ([x : Int]) x) : (-> Int Int))
(check-type (lambda ([x : (Box Int)]) x) : (-> (Box Int) (Box Int)))
(check-type (lambda once ([x : Int]) ()) : (-o Int Unit))
(check-type (if #t 3 4) : Int)
(check-type (if 4 3 4) #:fail)
