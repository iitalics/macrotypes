#lang s-exp "../linear-mixed/mixed.rkt"

; in unrestricted language, usage doesn't matter
(let ([x (tup 1 2)])
  0)

(let ([x (tup 1 2)])
  (tup x x))


; move to linear language (l <expr>)
(l (let ([x (tup 1 2)])
     (let* ([(a b) x])
       a)))

; (fails; linearity violation)
#;(l (let ([x (tup 1 2)])
       0))

; (fails; box not valid outside of linear lang
#;(l (let ([x (box 3)])
       x))


; share linear values with (share <expr>)
(l (share (tup 1 2)))

(l (let ([f (share (lambda ([x : Int]) x))])
     (share (tup (f 3) (f 4)))))
