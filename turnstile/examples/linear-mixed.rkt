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

  (define (->unrestricted ty)
    (syntax-parse ty
      [(~-o σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (-> τ ...)))]
      [(~-> σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (-> τ ...)))]
      [(~⊗ σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (× τ ...)))]
      [(~× σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (× τ ...)))]
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
      [(unrestricted? ty)
       (type+var-set ty (empty-var-set))]
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


  (define linear-sublanguage?
    (make-parameter #f))

  )



(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         let let*
         lin
         share
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
   #:when [linear-sublanguage?]
   #:when (> (stx-length #'(e ...)) 1)
   [⊢ e ≫ e- ⇒ σ] ...
   #:with σ_tup #'(⊗ σ ...)
   #:with σ_tup+ (let ([Vs (map type-var-set (syntax-e #'(σ ...)))])
                   (type+var-set #'σ_tup (lin/seq Vs)))
   --------
   [⊢ (#%app- list- e- ...) ⇒ σ_tup+]]

  ;;; [unrestricted]
  [(_ e ... ) ≫
   #:when (not [linear-sublanguage?])
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (#%app- list- e- ...) ⇒ (× τ ...)]])



(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   #:when [linear-sublanguage?]
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
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out+]]

  ;;; [unrestricted]
  [(_ ([x:id rhs] ...) e) ≫
   #:when (not [linear-sublanguage?])
   [⊢ rhs ≫ rhs- ⇒ τ] ...
   [[x ≫ x- : τ] ... ⊢ e ≫ e- ⇒ τ_out]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ τ_out]])



(define-typed-syntax let*
  [(_ ([(x:id y:id) rhs]) e) ≫
   #:when [linear-sublanguage?]
   [⊢ rhs ≫ rhs- ⇒ σ]
   #:with (~or (~⊗ σ1 σ2) (~post (~fail (format "cannot destructure non-pair type: ~a"
                                                (type->str #'σ)))))
          (->linear #'σ)
   #:with σ/x (type+linear-var #'σ1 #'x)
   #:with σ/y (type+linear-var #'σ2 #'y)

   [[x ≫ x- : σ/x] [y ≫ y- : σ/y] ⊢ e ≫ e- ⇒ σ_out]
   #:with σ_out+ (let ([V-rhs (type-var-set #'σ)]
                       [V-x (type-var-set #'σ/x)]
                       [V-y (type-var-set #'σ/y)]
                       [V-out (type-var-set #'σ_out)])
                   (type+var-set #'σ_out
                                 (lin/seq
                                  (list V-rhs (lin/introduce (list V-x V-y)
                                                             #:in V-out)))))
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (let- ([tmp rhs-])
            (let- ([x- (#%app- car tmp)]
                   [y- (#%app- cadr tmp)])
              e-))
      ⇒ σ_out+]]

  ;;; [unrestricted]
  [(_ ([(x:id y:id) rhs]) e) ≫
   #:when (not [linear-sublanguage?])
   [⊢ rhs ≫ rhs- ⇒ τ]
   #:with (~or (~× τ1 τ2) (~post (~fail (format "cannot destructure non-pair type: ~a"
                                                (type->str #'τ)))))
          #'τ

   [[x ≫ x- : τ1] [y ≫ y- : τ2] ⊢ e ≫ e- ⇒ τ_out]
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (let- ([tmp rhs-])
            (let- ([x- (#%app- car tmp)]
                   [y- (#%app- cadr tmp)])
              e-))
      ⇒ τ_out]]


  [(_ () e) ≫
   --------
   [≻ e]]
  [(_ ([x:id r] vs ...) e) ≫
   --------
   [≻ (let ([x r]) (let* (vs ...) e))]]
  [(_ ([(x:id y:id) r] vs ...+) e) ≫
   --------
   [≻ (let* ([(x y) r]) (let* (vs ...) e))]])




(define-typed-syntax lin
  [(_ _) ≫
   #:when [linear-sublanguage?]
   --------
   [#:error "cannot use 'lin' within linear language"]]

  [(_ lin-expr) ≫
   #:when (not [linear-sublanguage?])
   #:with (e- σ)
   (parameterize ([linear-sublanguage? #t])
     (syntax-parse #'lin-expr
       [(~and e [~⊢ e ≫ e- ⇒ σ])
        #'(e- σ)]))

   #:fail-unless (unrestricted? #'σ)
   (format "linear type ~a cannot leave linear boundary"
           (type->str #'σ))
   --------
   [⊢ e- ⇒ σ]])



(define-typed-syntax share
  [(_ e) ≫
   #:when [linear-sublanguage?]
   [⊢ e ≫ e- ⇒ σ]
   #:with τ (->unrestricted #'σ)
   #:fail-unless (unrestricted? #'τ)
   (format "cannot share type ~a" (type->str #'τ))
   #:with τ+ (type+var-set #'τ (type-var-set #'σ))
   --------
   [⊢ e- ⇒ τ+]]

  [(_ _) ≫
   #:when (not [linear-sublanguage?])
   --------
   [#:error "cannot use 'share' outside of linear language"]])
