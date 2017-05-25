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
      [(~-> τ ...) (andmap unrestricted? (syntax-e #'(τ ...)))]
      [(~× τ ...)  (andmap unrestricted? (syntax-e #'(τ ...)))]
      [_ #f]))

  (define (->linear ty)
    (syntax-parse ty
      [(~-> τ ...) ((current-type-eval) (syntax/loc ty (-o τ ...)))]
      [(~× τ ...)  ((current-type-eval) (syntax/loc ty (⊗ τ ...)))]
      [_ ty]))



  (define (empty-var-set)
    (immutable-free-id-set))

  (define (type-var-set ty)
    (or (syntax-property ty '#%vars)
        (empty-var-set)))

  (define (type+var-set ty vars)
    (syntax-property ty '#%vars vars))

  (define (type+linear-var ty src)
    (cond
      [(unrestricted? ty) ty]
      [else
       (let ([id (put-props (generate-temporary src)
                            'orig src)])
         ; NOTE: id does NOT BECOME REAL SYNTAX
         ;       it's just used to keep track of a linear variable's usage
         ;       i'm essentially just using free-id-set's because racket has
         ;       pretty weak hash-table operations (e.g. intersect, union)
         ;       compared to sets
         (type+var-set ty (immutable-free-id-set (list id))))]))



  (define (lin/seq Vs)
    (for/fold ([acc (empty-var-set)])
              ([V (in-list Vs)])
      (for ([v (in-set (set-intersect V acc))])
        (raise-syntax-error #f
                            "linear variable used more than once"
                            (syntax-property v 'orig)))
      (set-union V acc)))

  (define (lin/introduce Vs #:in V-body)
    (let ([V-new (foldl set-union (empty-var-set) Vs)])
      (for ([v (in-set (set-subtract V-new V-body))])
        (raise-syntax-error #f
                            "linear variable unused"
                            (syntax-property v 'orig)))
      (set-subtract V-body V-new)))

  )



(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         let
         #%module-begin
         (rename-out [top-interaction #%top-interaction]))





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
   #:with σ_tup #'(⊗ σ ...)
   #:with σ_tup+ (let ([Vs (map type-var-set (syntax-e #'(σ ...)))])
                   (type+var-set #'σ_tup (lin/seq Vs)))
   --------
   [⊢ (#%app- list- e- ...) ⇒ σ_tup+]])


(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with (σ/x ...) (stx-map type+linear-var
                             #'(σ ...) #'(x ...))
   [[x ≫ x- : σ/x] ... ⊢ e ≫ e- ⇒ σ_out]
   #:with σ_out+ (let ([Vs-rhs (map type-var-set (syntax-e #'(σ ...)))]
                       [Vs-vars (map type-var-set (syntax-e #'(σ/x ...)))]
                       [V-out (type-var-set #'σ_out)])
                   (type+var-set #'σ_out
                                 (lin/seq (cons (lin/introduce Vs-vars #:in V-out)
                                                Vs-rhs))))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out+]])
