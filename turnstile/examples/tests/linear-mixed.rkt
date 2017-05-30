#lang s-exp "../linear-mixed.rkt"

(let ([x (tup 3 5)])
  (let* ([(a b) x])
    (+ a b)))
