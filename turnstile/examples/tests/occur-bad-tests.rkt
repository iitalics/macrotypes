#lang s-exp turnstile/examples/occur-bad
(require "rackunit-typechecking.rkt")


(check-not-type (read) : Int)

(check-type (let ([x (read)])
              (cond
                [(integer? x) x]
                [else 0]))
            : Int)
