#lang s-exp "../linear-mixed.rkt"

(let ([x (box 2)])
  (if #t
      x
      (begin (box 0))))
