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
  (define (sym-dif s0 . ss)
    (for*/fold ([s s0])
               ([s1 (in-list ss)]
                [x (in-set s1)])
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


  ; pattern expanders for dual types (e.g. ×/⊗ and ->/-o)
  (define-syntax ~pair
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(_ a b) #'(~or (~× a b) (~⊗ a b))]))))

  (define-syntax ~fun
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(_ a ...) #'(~or (~-> a ...) (~-o a ...))]))))




  ; set of current unused linear variables in context
  (define unused-lin-vars
    (immutable-free-id-set))


  ; like make-variable-like-transformer, but for linear variables
  (define (make-linear-var-transformer ty-stx tag x)
    (define ty ((current-type-eval) ty-stx))
    (syntax-parser
      [:id
       (cond
         [(unrestricted? ty) (put-props x tag ty)]
         [(set-member? unused-lin-vars x)
          (set! unused-lin-vars (set-remove unused-lin-vars x))
          (put-props x tag ty)]
         [else
          (displayln (set->list unused-lin-vars))
          (raise-syntax-error #f "linear variable used more than once" this-syntax)])]

      [(id . args)
       #:with ap (datum->syntax this-syntax '#%app)
       (syntax/loc this-syntax
         (ap id . args))]))


  ; infer the type of every expression in es. introduces new linear variables
  ; given the form ([x : ty] ...). returns list (xs- ts es-) where xs- are the
  ; expanded versions of the variables, ts are the resulting type of the expressions,
  ; and es- are the expanded forms of the expressions.
  (define (infer/lin-vars es ctx-new)
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


  ; infer the type of every expression in es, but expect the linear variable
  ; usage in each expression to be the same.
  (define (infer/branch es
                        #:err [err (lambda (u expr)
                                     (raise-syntax-error #f
                                                         "linear variable may be unused"
                                                         u
                                                         expr))])
    (define ulv unused-lin-vars)
    (match (map (lambda (e)
                  (set! unused-lin-vars ulv)
                  (syntax-parse (infer/lin-vars (list e) '())
                    [(_ (σ) (e-))
                     (list #'σ #'e- unused-lin-vars)]))
                (syntax->list es))
      [(list (list ts es- ulvs) ...)

       (let ([similar (apply set-intersect ulvs)])
         (for ([src (in-syntax es)]
               [ulv (in-list ulvs)])
           (for ([v (in-set (set-subtract ulv similar))])
             (err v src))))

       (set! unused-lin-vars (first ulvs))
       (list ts es-)]))

  )

(define-syntax with-new-linear-vars
  (syntax-parser
    [(_ ([x σ] ...) body)
     (let ([lxs (immutable-free-id-set
                 (for/list ([x (in-syntax #'(x ...))]
                            [t (in-syntax #'(σ ...))]
                            #:when (not (unrestricted? ((current-type-eval) t))))
                   x))])
       (set! unused-lin-vars (set-union unused-lin-vars lxs))
       (let ([body- (local-expand #'body 'expression '())])
         (for ([u (in-set (set-intersect unused-lin-vars lxs))])
           (raise-syntax-error #f "linear variable unused" u))
         body-))]))


(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         begin let let* if #%app lambda
         box tup
         #%module-begin
         (rename-out [top-interaction #%top-interaction]
                     [lambda λ]))





; typed syntax

(provide (typed-out [[THING : (× Int Int)] THING]
                    [+ : (-> Int Int Int)]))
(define THING '(1 2))



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
   #:with ((x- ...) (σ_out) (e-)) (infer/lin-vars #'{e} #'([x : σ] ...))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax let*
  [(_ ([(x:id y:id) rhs] rest ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ]
   #:with (~or (~pair σ1 σ2)
               (~post (~fail (format "cannot destructure non-pair type ~a"
                                     (type->str #'σ)))))  #'σ
   #:with ((x- y-) (σ_out) (e-)) (infer/lin-vars #'{(let* (rest ...) e)} #'([x : σ1] [y : σ2]))
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


(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- ⇒ ~Bool]
   #:with ((σ1 σ2) (e2- e3-)) (infer/branch #'{e2 e3})
   [σ2 τ= σ1 #:for e2]
   --------
   [⊢ (if- e1- e2- e3-) ⇒ σ1]])


(define-typed-syntax #%app
  [(_ fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ σ_fun]
   #:with (~fun σ_in ... σ_out) #'σ_fun
   #:fail-unless (stx-length=? #'(σ_in ...) #'(arg ...))
   (format "wrong number of arguments to function, expected ~a, got ~a"
           (stx-length #'(σ_in ...))
           (stx-length #'(arg ...)))

   [⊢ arg ≫ arg- ⇒ σ_arg] ...
   [σ_arg τ= σ_in #:for arg] ...
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])


(define-typed-syntax lambda
  [(_ ([x:id (~datum :) ty:type] ...) body) ≫
   #:with ((x- ...) (σ_out) (body-)) (infer/lin-vars #'{body}
                                                     #'([x : ty] ...))
   --------
   [⊢ (λ- (x- ...) body-) ⇒ (-o ty.norm ... σ_out)]])
