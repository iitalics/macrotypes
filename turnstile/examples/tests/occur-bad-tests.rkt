#lang s-exp turnstile/examples/occur-bad
(require "rackunit-typechecking.rkt")


(check-not-type (read) : Int)

(check-type (let ([x (read)])
              (cond
                [(integer? x) x]
                [else 0]))
            : Int)

(check-type (let ([x (read)])
              (cond
                [(string? x) x]
                [(integer? x) "<number>"]
                [else (error "invalid input")]))
            : String)

(typecheck-fail (let ([x (read)])
                  (cond
                    [#f  "some string"]
                    [else x]))
                #:with-msg "expected String, given Any")
