#lang racket
(require turnstile
         (for-syntax racket syntax/parse)
         (for-meta 2 syntax/parse))


(provide (rename-out [mod-begin #%module-begin]
                     [top #%top-interaction]
                     [do-nothing/τ um])
         unit)


(define-base-type Unit)
(define-type-constructor → #:arity = 2)
(define-binding-type ∀ #:arity = 1 #:bvs = 1)

(begin-for-syntax
  ;; syntax property utils
  (define prop syntax-property)
  (define (attach s . l)
    (let trav ([s s] [l l])
      (match l
        [(list* k v l-rest)
         (trav (syntax-property s k v)
               l-rest)]
        [(list) s])))

  ;; type stuff
  (define (eval-type s)
    ((current-type-eval) s))

  ;; type to string
  (define (type->string t)
    (define ->dat
      (syntax-parser
        [(~→ t u) `(→ ,(->dat #'t)
                      ,(->dat #'u))]
        [(~∀ (a) t) `(∀ (,(syntax-e #'a))
                        ,(->dat #'t))]
        [~Unit 'Unit]
        [x:id (syntax-e #'x)]))
    (format "~a" (->dat t))))

(begin-for-syntax
  (require rackunit)
  ;; a context (Γ) is a syntax list of:
  ;;   (TVAR a)
  ;;   (EXVAR a)
  ;;   (MARK a)
  ;;   (a = τ)
  ;;   (x : τ)

  ; this matches one of those by the head symbol,
  ; and is used in the following pattern expanders
  (define-syntax-class (Γ-var hd var)
    (pattern (a b)
             #:when (symbol=? (syntax-e #'a) hd)
             #:when (bound-identifier=? #'b var)))

  ; this matchs the constraint relation (a = τ)
  (define-syntax-class (Γ-= var)
    (pattern (a (~datum =) b)
             #:when (bound-identifier=? #'a var)
             #:with rhs #'b))

  (define-syntax ~MARK
    (pattern-expander
     (syntax-parser [(_ v) #'(~var _ (Γ-var 'MARK v))])))
  (define-syntax ~TYVAR
    (pattern-expander
     (syntax-parser [(_ v) #'(~var _ (Γ-var 'TVAR v))])))
  (define-syntax ~EXVAR
    (pattern-expander
     (syntax-parser [(_ v) #'(~var _ (Γ-var 'EXVAR v))])))


  ;; does T contain the variable v?
  (define (fv-in? v T)
    (syntax-parse T
      [~Unit #f]
      [(~→ t u) (or (fv-in? v #'t) (fv-in? v #'u))]
      [(~∀ (a) t) (and (not (bound-identifier=? #'a v))
                       (fv-in? v #'t))]
      [x:id (bound-identifier=? #'x v)]))

  (syntax-parse (eval-type #'(∀ (a) (∀ (b) (→ a Unit))))
    [(~∀ (a) (~∀ (b) T))
     (check-true (fv-in? #'a #'T))
     (check-false (fv-in? #'b #'T))])


  ;; apply all exvar constraints in a context to a type
  (define (apply-ctx ctx T)
    (define-values (xs τs)
      (for/fold ([xs '()] [τs '()])
                ([e (in-syntax ctx)])
        (syntax-parse e
          [(a (~datum =) rhs)
           (values (cons #'a xs)
                   (cons #'rhs τs))]
          [_ (values xs τs)])))
    (substs τs xs T))

  (syntax-parse (eval-type #'(∀ (a) (∀ (b) (→ a Unit))))
    [(~∀ (a) (~∀ (b) T))
     #:with Γ #'[(a = Unit) (EXVAR u) (u = (→ Unit Unit))]
     (check-equal? (type->string (apply-ctx #'Γ #'T))
                   "(→ Unit Unit)")])

  ;; is the type an exvar?
  (define (exvar? a)
    (and (identifier? a)
         (prop a 'exvar?)))

  ;; a monotype is a type without quantifications
  (define (monotype? T)
    (syntax-parse T
      [~Unit #t]
      [(~→ t u) (and (monotype? #'t)
                     (monotype? #'u))]
      [(~∀ (a) _) #f]
      [x:id #t]))

  (syntax-parse (eval-type #'(∀ (a) (→ a Unit)))
    [(~and T (~∀ (a) t))
     (check-true (monotype? #'t))
     (check-false (monotype? #'T))])


  ; algorithmic subtyping
  (define (<: ctx t u)
    (with-syntax ([Γ ctx])
      (syntax-parse (list t u)
        ; <:Unit
        [(~Unit ~Unit)
         #'Γ]

        ; <:Var / <:Exvar
        [(x:id y:id) #:when (bound-identifier=? #'x #'y)
         #'Γ]

        ; <:InstantiateL
        [(^a:id A)
         #:when (exvar? #'^a)
         #:when (not (fv-in? #'^a #'A))
         (</:= #'Γ #'^a #'A)]

        ; <:InstantiateR
        [(A ^a:id)
         #:when (exvar? #'^a)
         #:when (not (fv-in? #'^a #'A))
         (</=: #'Γ #'A #'^a)]

        ; <:-→
        [((~→ A1 A2) (~→ B1 B2))
         #:with Θ (<: #'Γ #'B1 #'A1)
         #:with (A2- B2-) (apply-ctx #'Θ #'(A2 B2))
         (<: #'Θ #'A2- #'B2-)]

        ; <:∀L
        [((~∀ (a) A) B)
         #:with ^a (attach (generate-temporary #'a) 'exvar? #t)
         #:with A- (subst #'^a #'a #'A)
         #:with Γ- #'[(EXVAR ^a) (MARK ^a) . Γ]
         #:with [_ ... (~MARK #'^a) . Δ] (<: #'Γ- #'A- #'B)
         #'Δ]

        ; <:∀R
        [(A (~∀ (a) B))
         #:with Γ- #'[(TYVAR a) . Γ]
         #:with [_ ... (~TYVAR #'a) . Δ] (<: #'Γ- #'A #'B)
         #'Δ]

        [_ (raise 'no-subtype)])))

  ; instantiation (left)
  (define (</:= ctx var T)
    (with-syntax ([Γ ctx] [^a var])
      (syntax-parse T
        ; InstLSolve
        [τ
         #:when (monotype? #'τ)
         #:with [γ- ... (~EXVAR #'^a) γ ...] #'Γ
         #'[γ- ... (^a = τ) γ ...]]

        ; InstLReach
        [^b:id
         #:when (exvar? #'^b)
         #:with [γR ... (~EXVAR #'^b) γM ... (~EXVAR #'^a) γL ...] #'Γ
         #'[γR ... (^b = ^a) γM ... (EXVAR ^a) yL ...]]

        ; InstLArr
        [(~→ A1 A2)
         #:with [γ- ... (~EXVAR #'^a) γ ...] #'Γ
         #:with (tmp1 tmp2) (generate-temporaries #'(^a ^a))
         #:with (~∀ (^a1) (~∀ (^a2) arrow))
         (eval-type #'(∀ (tmp1) (∀ (tmp2) (→ tmp1 tmp2))))
         #:with Γ- #'[γ- ... (^a = arrow) (EXVAR ^a1) (EXVAR ^a2) γ ...]
         #:with Θ (</=: #'Γ- #'A1 #'^a1)
         #:with (A2-) (apply-ctx #'Θ #'(A2))
         (</:= #'Θ #'^a2 #'A2-)]

        ; InstLAllR
        [(∀ (b) B)
         #:with Γ- #'[b . Γ]
         #:with [_ ... (TYVAR #'b) . Δ] (</:= #'Γ- #'^a #'B)
         #'Δ]

        [_ (raise 'no-instantiate)])))

  ; instantiation (right)
  (define (</=: ctx T var)
    (with-syntax ([Γ ctx] [^a var])
      (syntax-parse T
        ; InstRSolve
        [τ
         #:when (monotype? #'τ)
         #:with [γ- ... (~EXVAR #'^a) γ ...] #'Γ
         #'[γ- ... (^a = τ) γ ...]]

        ; InstRReach
        [^b:id
         #:when (exvar? #'^b)
         #:with [γR ... (~EXVAR #'^b) γM ... (~EXVAR #'^a) γL ...] #'Γ
         #'[γR ... (^b = ^a) γM ... (EXVAR ^a) yL ...]]

        ; InstRArr
        [(~→ A1 A2)
         #:with [γ- ... (~EXVAR #'^a) γ ...] #'Γ
         #:with (tmp1 tmp2) (generate-temporaries #'(^a ^a))
         #:with (~∀ (^a1) (~∀ (^a2) arrow))
         (eval-type #'(∀ (tmp1) (∀ (tmp2) (→ tmp1 tmp2))))
         #:with Γ- #'[γ- ... (^a = arrow) (EXVAR ^a1) (EXVAR ^a2) γ ...]
         #:with Θ (</:= #'Γ- #'^a1 #'A1)
         #:with (A2-) (apply-ctx #'Θ #'(A2))
         (</=: #'Θ #'A2- #'^a2)]

        ; InstRAllL
        [(∀ (b) B)
         (raise 'meh)]

        [_ (raise 'no-instantiate)])))

  )



(begin-for-syntax
  ;; kinds of exceptions
  (struct exn:no-checking exn:fail:syntax ())
  (struct exn:no-synthesis exn:fail:syntax ())
  (struct exn:no-apply exn:fail:syntax ())

  (define (raise-no-checking s)
    (raise (exn:no-checking "no checking rule"
                            (current-continuation-marks)
                            (list s))))

  (define (raise-no-apply s)
    (raise (exn:no-apply "expression cannot be applied"
                         (current-continuation-marks)
                         (list s))))

  (define (infer e #:Γ ctx)
    (let* ([e* (attach e
                       'ctx⇐ ctx
                       'ty⇐ #f)]
           [e- (local-expand e* 'expression '())])
      (list e-
            (or (prop e- 'ty⇒)
                (raise-syntax-error #f "no type inferred!" e))
            (or (prop e- 'ctx⇒)
                (and (displayln "warning: no output context")
                     ctx)))))

  (define (check e τ #:Γ ctx)
    (let* ([e* (attach e
                       'ctx⇐ ctx
                       'ty⇐ τ)]
           [e- (local-expand e* 'expression '())])
      (list e-
            (or (prop e- 'ctx⇒)
                (and (displayln "warning: no output context")
                     ctx)))))


  (define (typed-transformer out-stx τ)
    (make-set!-transformer
     (syntax-parser
       [((~literal set!) a ...)
        (raise-syntax-error #f "cannot set! typed syntax" this-syntax)]
       [(a . b)
        (with-syntax ([ap (datum->syntax this-syntax '#%app)])
          #'(ap a . b))]

       [_ #:when (prop this-syntax 'ty⇐)
          (raise-no-checking this-syntax)]

       [_ ; infer
        #:with Γ (prop this-syntax 'ctx⇐)
          (attach out-stx
                  'ctx⇒ #'Γ
                  'ty⇒ (eval-type τ))])))
  )


(define (do-nothing x) (cons 'um x))
(define-syntax do-nothing/τ
  (typed-transformer #'do-nothing
                     #'(→ Unit Unit)))




(define-syntax mod-begin
  (syntax-parser
    [(_ ...) #'(#%module-begin)]))



(define-syntax top
  (syntax-parser
    [(_ . e)
     #:with (e- τ Γ) (infer #'e #:Γ '())
     #:with τ/s (type->str #'τ)
     #'(printf "~a : ~a\nΓ = ~s\n"
               e-
               'τ/s
               'Γ)]))



(define-syntax unit
  (syntax-parser
    [(_) ; check
     #:with Γ (prop this-syntax 'ctx⇐)
     #:attr in (prop this-syntax 'ty⇐) #:when (attribute in)
     #:fail-unless (Unit? #'in) "expected Unit type"
     (attach #'null
             'ctx⇒ #'Γ)]

    [(_) ; infer
     #:with Γ (prop this-syntax 'ctx⇐)
     (attach #'null
             'ty⇒ (eval-type #'Unit)
             'ctx⇒ #'Γ)]))
