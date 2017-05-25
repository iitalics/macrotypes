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



  (define (empty-var-set)
    (immutable-free-id-set))

  (define (type/linear-var ty src)
    (cond
      [(unrestricted? ty) ty]
      [else
       (let ([id (put-props (generate-temporary src)
                            'orig src)])
         (put-props ty
                    '#%vars (immutable-free-id-set (list id))))]))

  (define (type-var-set ty)
    (or (syntax-property ty '#%vars)
        (empty-var-set)))

  (define (type-put-vars ty vars)
    (put-props ((current-type-eval) ty)
               '#%vars vars))


  ; this must be used for expansion instead of (current-type-eval) because
  ; the latter adds things to 'orig that we don't want.
  (define (linear-expand ty)
    (local-expand ty 'expression '()))

  )

(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         let
         #%module-begin
         (rename-out [top-interaction #%top-interaction]))


; macros for combining linear information encoded in types

(define-syntax lin/seq
  (syntax-parser
    [(_ σ ... #:as σ_out)
     (let ([var-sets (map type-var-set (syntax-e #'(σ ...)))])
       (type-put-vars #'σ_out
                      (for/fold ([vars (empty-var-set)])
                                    ([vs (in-list var-sets)])
                            (for ([v (in-set (set-intersect vs vars))])
                              (raise-syntax-error #f
                                                  "linear variable used more than once"
                                                  (syntax-property v 'orig)))
                            (set-union vs vars))))]))

(define-syntax lin/introduce
  (syntax-parser
    [(_ σ ... #:in σ_body #:as σ_out)
     (let* ([new-vars (for/fold ([new-vars (empty-var-set)])
                                ([t (in-list (syntax-e #'(σ ...)))])
                        (set-union new-vars (type-var-set t)))]
            [body-vars (type-var-set #'σ_body)])
       (for ([v (in-set (set-subtract new-vars body-vars))])
         (raise-syntax-error #f
                             "linear variable unused"
                             (syntax-property v 'orig)))
       (type-put-vars #'σ_out
                      (set-subtract body-vars new-vars)))]))




; typed syntax

(define-typed-syntax (top-interaction . e) ≫
  [⊢ e ≫ e- ⇒ σ]
  --------
  [≻ (#%app- printf- "~s : ~a\n"
             e-
             '#,(type->str #'σ))])



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
   #:with σ_out+ (linear-expand
                  #'(lin/seq σ ... #:as (⊗ σ ...)))
   --------
   [⊢ (#%app- list- e- ...) ⇒ σ_out+]])



(define-typed-syntax let
  [(_ ([x rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with (σ+ ...) (stx-map type/linear-var
                            #'(σ ...) #'(x ...))
   [[x ≫ x- : σ+] ... ⊢ e ≫ e- ⇒ σ_out]
   #:with σ_out+ (linear-expand
                  #'(lin/introduce σ+ ...
                                   #:in σ_out
                                   #:as σ_out))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out+]])
