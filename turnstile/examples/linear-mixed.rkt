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
  (require syntax/id-set)

  ; put multiple syntax properties onto the given syntax object
  ; (put-props stx key1 val1 key2 val2 ...) -> stx-
  (define-syntax (put-props stx)
    (syntax-case stx ()
      [(_ expr key val . rst)
       #'(put-props (syntax-property expr key val) . rst)]
      [(_ expr)
       #'expr]))


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



  (define (type/linear-var ty src)
    (cond
      [(unrestricted? ty) ty]
      [else
       (let ([id (put-props (generate-temporary src)
                            'orig src)])
         (put-props ty
                    '#%vars (immutable-free-id-set id)))]))

  )

(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         let
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


(define-typed-syntax let
  [(_ ([x rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with (σ+ ...) (stx-map type/linear-var
                            #'(σ ...) #'(x ...))
   [[x ≫ x- : σ+] ... ⊢ e ≫ e- ⇒ σ_out]
   --------
   [⊢ (let- ([x- rhs-] ...) e-)
      ; TODO: introduce variable from σ+
      ⇒ σ_out]])
