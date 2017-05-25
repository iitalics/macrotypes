#lang turnstile/lang

; primitives
(define-base-types Unit Int Bool Str)

; unrestricted
(define-type-constructor -> #:arity >= 1)
(define-type-constructor × #:arity > 1)

; linear
(define-type-constructor -o #:arity >= 1)
(define-type-constructor ⊗ #:arity > 1)
(define-base-type Loc)
(define-type-constructor Box #:arity = 1)


(begin-for-syntax

  (define unrestricted?
    (syntax-parser
      [(~or ~Unit ~Int ~Bool ~Str) #t]
      [(-> τ ...) (andmap unrestricted? (syntax-e #'(τ ...)))]
      [(× τ ...)  (andmap unrestricted? (syntax-e #'(τ ...)))]
      [_ #f]))

  (define (->linear ty)
    (syntax-parse ty
      [(-> τ ...) ((current-type-eval) (syntax/loc ty (-o τ ...)))]
      [(× τ ...)  ((current-type-eval) (syntax/loc ty (⊗ τ ...)))]
      [_ ty]))

  )
