#lang s-exp "../linear-mixed.rkt"

(lin (let* ([p (tup 1 2)]
            [(x y) p])
       x))

(lin (let* ([p (tup 1 2)]
            [p* (share p)])
       (share (tup p* p*))))
