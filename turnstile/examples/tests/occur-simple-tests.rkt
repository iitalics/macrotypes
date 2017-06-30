#lang s-exp turnstile/examples/occur-simple
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

; i am worried about free-identifier=? causing problems
; which would be exemplified here (the latter bound 'x'
; thinking that the deduction (integer? x) applies to it
; as well).
; but this does fail as it's supposed to, so we're ok.
(typecheck-fail (let ([x (read)])
                  (cond
                    [(integer? x)
                     (let ([x "hi"])
                       (if #t x 0))]
                    [else 1])))
