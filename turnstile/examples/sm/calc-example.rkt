#lang s-exp "calc.rkt"

; typecheck failure, as expected:
;   (+ 1 #f)

; typechecks, but elaborates incorrectly when run
(if (< 1 2)
    3
    4)

; the RPN translator in sm.rkt is supposed to thread
; the variable representing the stack, e.g.
;   1 2 + .d
; becomes
;   (let* ([s1 (cons 1 s0)]
;          [s2 (cons 2 s1)]
;          [s3 (@+ s2)])
;     (@display s3))
; it does this using the syntax parameter 'stack',
; which is parameterized to different rename-transformers
; at every level (see ==> macro in sm.rkt)

; unfortunately, typechecking fully expands each
; elaboration, so they all get the same top-level
; stack variable, e.g.
;   (let* ([s1 (cons 1 s0)]
;          [s2 (cons 2 s0)]
;          [s3 (@+ s0)])
;     (@display s0))
