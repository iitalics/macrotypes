#lang s-exp "../linear.rkt"

(let ([b (box 3)])
  (if #t
      b
      (begin (box 0))))
