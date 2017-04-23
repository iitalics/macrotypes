#lang racket
(require turnstile
         (for-syntax racket syntax/parse
                     rackunit)
         (for-meta 2 syntax/parse))


(provide (rename-out [mod-begin #%module-begin]
                     [top #%top-interaction]
                     [do-nothing/τ um])
         unit)


; types
(define-base-type Unit)
(define-type-constructor → #:arity = 2)
(define-binding-type ∀ #:arity = 1 #:bvs = 1)

; existential variables
(define-type-constructor Exv #:arity = 1)

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
        [(~Exv _) `__]
        [x:id (syntax-e #'x)]))
    (format "~a" (->dat t))))



;; existential variables (holes)
(begin-for-syntax
  (define next-ex-uid (box 0))

  (define (generate-exv [id-stx #'a])
    (define uid (unbox next-ex-uid))
    (set-box! next-ex-uid (add1 uid))
    (with-syntax ([uid/#%t (mk-type #`(quote #,uid))])
      (eval-type (syntax/loc id-stx
                   (Exv uid/#%t)))))

  (define (Exv=? e1 e2)
    (syntax-parse (list e1 e2)
      #:literals (quote)
      [((~Exv 'a) (~Exv 'b))
       (equal? (syntax-e #'a) (syntax-e #'b))]
      [_ #f]))

  )


;; contexts
(begin-for-syntax

  (define (exv/id=? a b)
    (cond
      [(and (identifier? a) (identifier? b))
       (bound-identifier=? a b)]
      [(and (Exv? a) (Exv? b))
       (Exv=? a b)]
      [else
       (equal? a b)]))

  ; split a context in half by the specified key and second elem
  (define (ctx-split-one ctx key snd)
    (define-values (L R)
      (splitf-at ctx
                 (negate (lambda (e)
                           (and (symbol=? (first e) key)
                                (exv/id=? snd (second e)))))))
    (list L (rest R)))

  (let ([e1 (generate-exv)]
        [e2 (generate-exv)])
    (check-equal? (ctx-split-one (list (list '▹ e1)
                                       (list ': #'x e2)
                                       (list '▹ e2))
                                 ': #'x)
                  (list (list (list '▹ e1))
                        (list (list '▹ e2)))))


  ; split a context into parts by specifying multiple keys and elems
  (define (ctx-split ctx . keys)
    (define (evens lst)
      (if (null? lst) '()
          (cons (car lst) (odds (cdr lst)))))
    (define (odds lst)
      (if (null? lst) '()
          (evens (cdr lst))))
    (foldr (lambda (key snd ctxs)
             (append (ctx-split-one (first ctxs) key snd)
                     (rest ctxs)))
           (list ctx)
           (evens keys)
           (odds keys)))

  (let ([e1 (generate-exv)]
        [e2 (generate-exv)]
        [e3 (generate-exv)])
    (check-equal? (ctx-split (list (list '▹ e1)
                                   (list ': 'x e2)
                                   (list 't (eval-type e2))
                                   (list ': 'y e3)
                                   (list '▹ e3))
                             't e2
                             ': 'y)
                  (list (list (list '▹ e1)
                              (list ': 'x e2))
                        (list)
                        (list (list '▹ e3)))))
)


;; inference helpers
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
