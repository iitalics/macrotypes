#lang turnstile

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

(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         #%module-begin
         (rename-out [top-interaction #%top-interaction]))



(define-typed-syntax (top-interaction . e) ≫
  [⊢ e ≫ e- ⇒ τ]
  --------
  [≻ (#%app- printf- "~s : ~a\n"
             e-
             '#,(type->str #'τ))])


(define-typed-syntax #%datum
  [(_ . k:exact-integer) ≫
   --------
   [⊢ 'k ⇒ Int]]
  [(_ . k:boolean) ≫
   --------
   [⊢ 'k ⇒ Bool]]
  [(_ . k:str) ≫
   --------
   [⊢ 'k ⇒ Str]])


(define-typed-syntax tup
  [(_ e ...) ≫
   #:when (> (stx-length #'(e ...)) 1)
   [⊢ e ≫ e- ⇒ σ] ...
   --------
   [⊢ (#%app- list- e- ...)
      ⇒ (× σ ...)]])
