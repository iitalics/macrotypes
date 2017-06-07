#lang turnstile
;; this contains the linear-only forms, and is not usable as a
;; stand-alone language. see "mixed.rkt" for a language which combines
;; syntax from this language and the "unrestric.rkt" language.

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
                  ~tuple)
         racket/unsafe/ops)

(provide (type-out -o ⊗ Box Loc !!)
         tup box unbox
         share copy
         let let* if lambda
         (rename-out [lambda λ]))

(require (for-syntax "new-infer.rkt"))


(begin-for-syntax
  (require syntax/id-set)
  (provide linear-type?
           linear-parse-fun
           linear-parse-tuple
           ;infer/lin-vars
           ;make-linear-var-transformer
           ;infer/branch
           )

  ; is the type a type whose values can only be bound once?
  ; e.g. all linear types except lump type (!! x)
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
      [(~!! (~-o σ ...)) (syntax/loc this-syntax (σ ...))]
      [_ #f]))

  (define linear-parse-tuple
    (syntax-parser
      [(~⊗ σ ...) (syntax/loc this-syntax (σ ...))]
      [_ #f]))


  ; set of current unused linear variables in context
  (define unused-lin-vars
    (immutable-free-id-set))



  ; like make-variable-like-transformer, but for linear variables
  (define (make-linear-variable-transformer x tag ty-stx)
    (define ty ((current-type-eval) ty-stx))

    (define re-apply
      (syntax-parser
        [(id . args)
         #:with ap (datum->syntax this-syntax '#%app)
         (syntax/loc this-syntax
           (ap id . args))]))

    (cond
      [(linear-type? ty)
       (set! unused-lin-vars (set-add unused-lin-vars x))
       (syntax-parser
         [:id
          (unless (set-member? unused-lin-vars x)
            (raise-syntax-error #f "linear variable used more than once" this-syntax))
          (set! unused-lin-vars (set-remove unused-lin-vars x))
          (attach x tag ty)]

         [_ (re-apply this-syntax)])]

      [else
       (syntax-parser
         [:id (attach x tag ty)]
         [_ (re-apply this-syntax)])]))

  (define-syntax (LINEAR stx)
    (syntax-case stx ()
      [(_ x tag ty)
       #'(make-linear-variable-transformer #'x 'tag #'ty)]))



  ; this stack is used by let, let* and λ to keep track of which
  ; variables were used before going out of scope

  (define unused-vars-stack '())

  ; push the current set of linear variables
  (define (push-linear-vars)
    (set! unused-vars-stack (cons unused-lin-vars unused-vars-stack)))

  ; pop the last set of linear variables, and throw errors for any variable
  ; still in the current set that wasn't in scope in the previous set
  (define (pop-linear-vars [err
                            (λ (v)
                              (raise-syntax-error #f "linear variable unused" v))])
    (let ([prev (car unused-vars-stack)])
      (set! unused-vars-stack (cdr unused-vars-stack))
      (set-for-each (set-subtract unused-lin-vars prev) err)))


  ; infer the type of every expression in es, but expect the linear variable
  ; usage in each expression to be the same. returns list (ts es-) where ts are
  ; the resulting type of the expressions, and es- are the expanded forms of the
  ; expressions.
  (define (infer/branch es
                        #:err [err (lambda (u expr)
                                     (raise-syntax-error #f
                                                         "linear variable may be unused"
                                                         u expr))])
    (define ulv unused-lin-vars)
    (match (map (syntax-parser
                  [e
                   #:do [(set! unused-lin-vars ulv)]
                   #:with (_ _ (e-) (σ)) (new-infer #'{e})
                   (list #'σ #'e- unused-lin-vars)])
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




; typed syntax

(define-typed-syntax tup
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ σ] ...
   --------
   [⊢ (#%app- list- e- ...) ⇒ (⊗ σ ...)]])


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
        (#%app- unsafe-set-box! tmp e-) tmp)
      ⇒ (Box σ)]])


(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Box σ)]
   #:with tmp (generate-temporary)
   --------
   [⊢ (let- ([tmp e-])
            (#%app- list- tmp (#%app- unsafe-unbox tmp)))
      ⇒ (⊗ Loc σ)]])

(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:do [(push-linear-vars)]
   #:with ((~new-typecheck
            [[LINEAR x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out])) '()
   #:do [(pop-linear-vars)]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax let*
  [(_ ([(x:id ...) rhs] . vars) e) ≫
   [⊢ rhs ≫ rhs- ⇒ (~and σ_tup
                         (~or (~parse (σ ...) ((current-parse-tuple) #'σ_tup))
                              (~post (~fail (format "expected tuple, cannot destructure type ~a"
                                                    (type->str #'σ_tup))))))]

   #:fail-unless (stx-length=? #'(σ ...) #'(x ...)) "wrong number of elements in tuple"

   #:do [(push-linear-vars)]
   #:with ((~new-typecheck
            [[LINEAR x ≫ x- : σ] ... ⊢ (let* vars e) ≫ e- ⇒ σ_out])) '()
   #:do [(pop-linear-vars)]

   --------
   [⊢ (-delist (x- ...) rhs- e-) ⇒ σ_out]]

  [(_ ([x:id rhs] . vars) e) ≫
   --------
   [≻ (let ([x rhs]) (let* vars e))]]
  [(_ () e) ≫
   --------
   [≻ e]])



(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- ⇐ U:Bool]
   ; [⊢ e2 ≫ e2- ⇒ σ1] [⊢ e3 ≫ e3- ⇒ σ2]
   #:with ((σ1 σ2) (e2- e3-)) (infer/branch #'{e2 e3})
   [σ2 τ= σ1 #:for e2]
   --------
   [⊢ (if- e1- e2- e3-) ⇒ σ1]])


(define-typed-syntax lambda
  [(_ ([x:id (~datum :) ty:type] ...) body) ≫
   ; [[x ≫ x- : ty] ⊢ body ≫ body- ⇒ σ_out]
   #:do [(push-linear-vars)]
   #:with ((~new-typecheck
            [[LINEAR x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ σ_out])) '()
   #:do [(pop-linear-vars)]
   --------
   [⊢ (λ- (x- ...) body-) ⇒ (-o ty.norm ... σ_out)]])


(define-typed-syntax share
  [(_ e) ≫
   ; by "branching" against an expression that definitely doesn't
   ; have any linear side effects (in this case, `()`), we can
   ; ensure that the other expression doesn't have side effects either
   #:with ((σ _) (e- _))
   (infer/branch #'{e (U:#%app)}
                 #:err
                 (λ (u expr)
                   (raise-syntax-error #f
                                       "may not share linear variable"
                                       u this-syntax)))
   --------
   [⊢ e- ⇒ (!! σ)]])


(define-for-syntax (copy-expr expr ty)
  (syntax-parse ty
    [(~⊗ σ ...)
     #:with (tmp ...) (generate-temporaries #'(σ ...))
     #:with (tmp+ ...) (stx-map copy-expr #'(tmp ...) #'(σ ...))
     #`(-delist (tmp ...) #,expr
                (#%app- list- tmp+ ...))]

    [(~Box σ)
     #:with e/unbox #`(#%app- unsafe-unbox #,expr)
     #:with e+ (copy-expr #'e/unbox #'σ)
     #'(#%app- box- e+)]

    [_ expr]))


(define-typed-syntax copy
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ σ_lump]
   #:with (~or (~!! σ)
               (~post (~fail (format "cannot copy type: ~a"
                                     (type->str #'σ_lump)))))
          #'σ_lump

   #:with e-/copied (copy-expr #'e- #'σ)
   --------
   [⊢ e-/copied ⇒ σ]])



; syntax: (-delist (x ...) <list-expr> <body-expr>)
; private macro for (unsafely) destructuring a list into variables
(define-syntax -delist
  (syntax-parser
    [(_ () l e) #'e]
    [(_ (x0:id x ...) l e)
     #:with tmp (generate-temporary)
     #'(let*- ([tmp l] [x0 (#%app- unsafe-car tmp)])
              (-delist (x ...) (#%app- unsafe-cdr tmp) e))]))
