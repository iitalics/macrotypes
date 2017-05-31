#lang turnstile
;; this contains the linear-only forms, common forms such as begin and #%app
;; should be reused from "unrestric.rkt"

(define-type-constructor !! #:arity = 1)
(define-type-constructor -o #:arity >= 1)
(define-type-constructor ⊗ #:arity > 1)
(define-type-constructor Box #:arity = 1)
(define-base-type Loc)

(require (prefix-in U: "unrestric.rkt")
         (only-in "unrestric.rkt"
                  current-parse-fun
                  current-parse-tuple
                  ~fun
                  ~tuple))

(provide (type-out -o ⊗ Box !!)
         tup box unbox share
         let let* if lambda
         (rename-out [lambda λ]))



(begin-for-syntax
  (require syntax/id-set)
  (provide linear-type?
           linear-parse-fun
           linear-parse-tuple
           infer/lin-vars
           infer/branch
           make-linear-var-transformer)

  ; put multiple syntax properties onto the given syntax object
  ; (put-props stx key1 val1 key2 val2 ...) -> stx-
  (define-syntax (put-props stx)
    (syntax-case stx ()
      [(_ expr key val . rst)
       #'(put-props (syntax-property expr key val) . rst)]
      [(_ expr)
       #'expr]))


  ;; is the given type linear?
  (define linear-type?
    (syntax-parser
      [(~-o _ ...) #t]
      [(~⊗ _ ...) #t]
      [(~Box _) #t]
      [~Loc #t]
      [_ #f]))


  (define linear-parse-fun
    (syntax-parser
      [(~-o σ ...) (syntax/loc this-syntax (σ ...))]
      [(~!! σ) (linear-parse-fun #'σ)]
      [_ #f]))

  (define linear-parse-tuple
    (syntax-parser
      [(~⊗ σ ...) (syntax/loc this-syntax (σ ...))]
      [(~!! σ) (linear-parse-tuple #'σ)]
      [_ #f]))




  ; set of current unused linear variables in context
  (define unused-lin-vars
    (immutable-free-id-set))


  ; procedure that gets called around linear variable usage
  (define current-with-linear-var
    (make-parameter values))


  ; like make-variable-like-transformer, but for linear variables
  (define (make-linear-var-transformer ty-stx tag x)
    (define ty ((current-type-eval) ty-stx))
    (syntax-parser
      [:id
       (cond
         [(not (linear-type? ty)) (put-props x tag ty)]
         [(set-member? unused-lin-vars x)
          (set! unused-lin-vars (set-remove unused-lin-vars x))
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
          #:with (τ ...) (stx-map (lambda (s) (or (detach s ':)
                                             (raise-syntax-error #f "no attached type" s)))
                                  #'(e- ...))
          (list #'(x- ...)
                #'(τ ...)
                #'(e- ...))])]))


  ; infer the type of every expression in es, but expect the linear variable
  ; usage in each expression to be the same. returns list (ts es-) where ts are
  ; the resulting type of the expressions, and es- are the expanded forms of the
  ; expressions.
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
                            #:when (linear-type? ((current-type-eval) t)))
                   x))])
       (set! unused-lin-vars (set-union unused-lin-vars lxs))
       (let ([body- (local-expand #'body 'expression '())])
         (for ([u (in-set (set-intersect unused-lin-vars lxs))])
           (raise-syntax-error #f "linear variable unused" u))
         body-))]))




; typed syntax

(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (⊗ σ1 σ2)]])


(define-typed-syntax box
  ; make a new box
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ σ]
   --------
   [⊢ (#%app- box- e-) ⇒ (Box σ)]]

  ; reuse a Loc
  [(_ l e) ≫
   [⊢ l ≫ l- ⇐ Loc]
   [⊢ e ≫ e- ⇒ σ]
   #:with tmp (generate-temporary)
   --------
   [⊢ (let- ([tmp l-])
        (#%app- set-box!- tmp e-) tmp)
      ⇒ (Box σ)]])


(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Box σ)]
   #:with tmp (generate-temporary)
   --------
   [⊢ (let- ([tmp e-])
            (#%app- list- tmp (#%app- unbox- tmp)))
      ⇒ (⊗ Loc σ)]])


(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with ((x- ...) (σ_out) (e-)) (infer/lin-vars #'{e} #'([x : σ] ...))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax let*
  [(_ ([(x:id ...) rhs] . vars) e) ≫
   [⊢ rhs ≫ rhs- ⇒ (~and σ_tup
                         (~or (~parse (σ ...) ((current-parse-tuple) #'σ_tup))
                              (~post (~fail (format "expected tuple, cannot destructure type ~a"
                                                    (type->str #'σ_tup))))))]

   #:fail-unless (stx-length=? #'(σ ...) #'(x ...)) "wrong number of elements in tuple"
   #:with ((x- ...) (σ_out) (e-)) (infer/lin-vars #'{(let vars e)} #'([x : σ] ...))
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (delist (x- ...) rhs- e-) ⇒ σ_out]]

  [(_ ([x:id rhs] . vars) e) ≫
   --------
   [≻ (let ([x rhs]) (let* vars e))]]
  [(_ () e) ≫
   --------
   [≻ e]])

; private macro for destructuring a list into variables
(define-syntax delist
  (syntax-parser
    [(_ () l e) #'e]
    [(_ (x0:id x ...) l e)
     #:with tmp (generate-temporary)
     #'(let*- ([tmp l] [x0 (#%app- car- tmp)]) (delist (x ...) (#%app- cdr- tmp) e))]))



(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- ⇐ U:Bool]
   #:with ((σ1 σ2) (e2- e3-)) (infer/branch #'{e2 e3})
   [σ2 τ= σ1 #:for e2]
   --------
   [⊢ (if- e1- e2- e3-) ⇒ σ1]])


(define-typed-syntax lambda
  [(_ ([x:id (~datum :) ty:type] ...) body) ≫
   #:with ((x- ...) (σ_out) (body-)) (infer/lin-vars #'{body}
                                                     #'([x : ty] ...))
   --------
   [⊢ (λ- (x- ...) body-) ⇒ (-o ty.norm ... σ_out)]])


(define-typed-syntax share
  [(_ e) ≫
   #:with ((σ _) (e- _))
   (infer/branch #'{e (U:#%app)}
                 #:err
                 (λ (u expr)
                   (raise-syntax-error #f
                                       "may not share linear variable"
                                       u this-syntax)))
   --------
   [⊢ e- ⇒ (!! σ)]]

   [(_ _) ≫
    --------
    [#:error "cannot use linear-only syntax here"]])
