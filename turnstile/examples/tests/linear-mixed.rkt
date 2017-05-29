#lang s-exp "../linear-mixed.rkt"

(let ([x (box 2)])
  (if #t
      x
      (begin x (box 0))))
