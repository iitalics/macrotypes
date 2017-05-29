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

  ;; symmetric difference implementation, because current impl for
  ;; id-tables is bugged
  (define (sym-dif s1 s2)
    (for/fold ([s s1])
              ([x (in-set s2)])
      (if (free-id-set-member? s x)
          (free-id-set-remove s x)
          (free-id-set-add s x))))


  ;; like split-at but on syntax objects, and returns a list instead
  ;; of values
  (define (stx-split-at stx pos)
    (let-values ([(a b) (split-at (syntax->list stx) pos)])
      (list (datum->syntax stx a)
            (datum->syntax stx b))))


  ; parameter to be set while expanding code that is in the linear
  ; sublanguage (within a (lin ...) form)
  (define linear-sublanguage?
    (make-parameter #f))



  ; is the given type unrestricted?
  (define unrestricted?
    (syntax-parser
      [(~or ~Unit ~Int ~Bool ~Str) #t]
      [(~-> τ ...) (andmap unrestricted? (syntax-e #'(τ ...)))]
      [(~× τ ...)  (andmap unrestricted? (syntax-e #'(τ ...)))]
      [_ #f]))


  ; set of current unused linear variables in context
  (define current-linear-context
    (make-parameter (immutable-free-id-set)))


  ; like make-variable-like-transformer, but for linear variables
  (define (make-linear-var-transformer ty tag x)
    (define ty- ((current-type-eval) ty))
    (syntax-parser
      [:id
       (cond
         [(unrestricted? ty) (put-props x tag ty)]
         [(set-member? [current-linear-context] x)
          [current-linear-context (set-remove [current-linear-context] x)]
          (put-props x tag ty)]
         [else
          (raise-syntax-error #f "linear variable used more than once" this-syntax)])]

      [(id . args)
       #:with ap (datum->syntax this-syntax '#%app)
       (syntax/loc this-syntax
         (ap id . args))]))


  ; infer the type of every expression in es. introduces new linear variables
  ; given the form ([x : ty] ...). returns list (xs- ts es-) where xs- are the
  ; expanded versions of the variables, ts are the resulting type of the expressions,
  ; and es- are the expanded forms of the expressions.
  (define (infer/linear es
                        [ctx-new '()]
                        #:ctx [ctx [current-linear-context]])
    (syntax-parse ctx-new
      [([x:id tag ty] ...)
       #:with (e ...) es
       (syntax-parse (local-expand #'(#%plain-lambda
                                      (x ...)
                                      (with-new-linear-vars ([x ty] ...)
                                        (let-syntax ([x (make-linear-var-transformer #`ty `tag #`x)] ...)
                                          (#%expression e) ...)))
                                   'expression
                                   null)
         #:literals (#%plain-lambda let-values #%expression)
         [(#%plain-lambda (x- ...)
                          (let-values ()
                            (let-values ()
                              (#%expression e-) ...)))
          #:with (τ ...) (stx-map (lambda (s) (or (syntax-property s ':)
                                             (raise-syntax-error #f "no attached type" s)))
                                  #'(e- ...))
          (list #'(x- ...)
                #'(τ ...)
                #'(e- ...))])]))

  )

(define-syntax with-new-linear-vars
  (syntax-parser
    [(_ ([x σ] ...) body)
     (let ([lxs (immutable-free-id-set
                 (for/list ([x (in-syntax #'(x ...))]
                            [t (in-syntax #'(σ ...))]
                            #:when (not (unrestricted? ((current-type-eval) t))))
                   x))])
       (parameterize ([current-linear-context
                       (set-union [current-linear-context] lxs)])
         (let ([body- (local-expand #'body 'expression '())])
           (for ([u (in-set (set-intersect [current-linear-context] lxs))])
             (raise-syntax-error #f "linear variable unused" u))
           body-)))]))


(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         begin let let*
         box tup
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


(define-typed-syntax box
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ σ]
   --------
   [⊢ (#%app- box- e-) ⇒ (Box σ)]])


(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (⊗ σ1 σ2)]])


(define-typed-syntax begin
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ σ] ...
   #:with σ_out (last (syntax-e #'(σ ...)))
   --------
   [⊢ (begin- e- ...) ⇒ σ_out]])


(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with ((x- ...) (σ_out) (e-)) (infer/linear #'(e) #'([x : σ] ...))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax let*
  [(_ ([(x:id y:id) rhs] rest ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ]
   #:with (~or (~⊗ σ1 σ2)
               (~post (~fail (format "cannot destructure non-pair type ~a"
                                     (type->str #'σ)))))  #'σ
   #:with ((x- y-) (σ_out) (e-)) (infer/linear #'((let* (rest ...) e)) #'([x : σ1] [y : σ2]))
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (let*- ([tmp rhs-]
              [x- (#%app- car tmp)]
              [y- (#%app- cadr tmp)]) e-)
      ⇒ σ_out]]

  [(_ ([x:id rhs] rest ...) e) ≫
   --------
   [≻ (let ([x rhs]) (let* (rest ...) e))]]
  [(_ () e) ≫
   --------
   [≻ e]])
