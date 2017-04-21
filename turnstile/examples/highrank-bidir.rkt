#lang racket
(require turnstile
         (for-syntax racket
                     syntax/parse))


(provide (rename-out [mod-begin #%module-begin]
                     [top #%top-interaction]
                     [do-nothing/τ um])
         unit)


(define-base-type Unit)
(define-type-constructor → #:arity = 2)
(define-binding-type ∀ #:arity = 1 #:bvs = 1)

(begin-for-syntax
  ;; kinds of exceptions
  (struct exn:no-checking exn:fail:syntax ())
  (struct exn:no-synthesis exn:fail:syntax ())
  (struct exn:no-apply exn:fail:syntax ())

  (define (raise-no-checking s)
    (raise (exn:no-checking "no checking rule"
                            (current-continuation-marks)
                            (list s))))

  (define (raise-no-synthesis s)
    (raise (exn:no-synthesis "no synthesis rule"
                             (current-continuation-marks)
                             (list s))))

  (define (raise-no-apply s)
    (raise (exn:no-apply "expression cannot be applied"
                         (current-continuation-marks)
                         (list s))))


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
    [(_)
     #:with Γ (prop this-syntax 'ctx⇐)
     #:attr in (prop this-syntax 'ty⇐) #:when (attribute in)
     #:fail-unless (Unit? #'in) "expected Unit type"
     (attach #'null
             'ctx⇒ #'Γ)]

    [(_)
     #:with Γ (prop this-syntax 'ctx⇐)
     (attach #'null
             'ty⇒ (eval-type #'Unit)
             'ctx⇒ #'Γ)]))
