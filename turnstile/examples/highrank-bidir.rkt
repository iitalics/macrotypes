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
  ; attaching & getting syntax properties
  (define prop syntax-property)
  (define (attach s . l)
    (let trav ([s s] [l l])
      (match l
        [(list* k v l-rest)
         (trav (syntax-property s k v)
               l-rest)]
        [(list) s])))

  ; evaluate a type
  (define (eval-type s)
    ((current-type-eval) s))

  ; convert type to string
  (define (type->string T)
    (define ->dat
      (syntax-parser
        [(~→ T1 T2) `(→ ,(->dat #'T1)
                        ,(->dat #'T2))]
        [(~∀ (X) T1) `(∀ (,(syntax-e #'X))
                         ,(->dat #'T1))]
        [~Unit 'Unit]
        [(~Exv _) '__]
        [X:id (syntax-e #'X)]))
    (format "~a" (->dat T)))

  ; a monotype is a type without quantifications
  (define (monotype? T)
    (syntax-parse T
      [(~→ T1 T2) (and (monotype? #'T1)
                       (monotype? #'T2))]
      [(~∀ (X) _) #f]
      [_ #t]))

  (check-not-false (monotype? (eval-type #'(→ Unit Unit))))
  (check-false (monotype? (eval-type #'(→ (∀ (x) x) Unit))))

  )



;; existential variables (holes)
(begin-for-syntax
  (define next-ex-uid (box 0))

  ; generate a unicode exvar
  (define (generate-exv [src-id #'a])
    (with-syntax ([uid/q* (mk-type #`(quote #,(if (identifier? src-id)
                                                  (gensym (syntax-e src-id))
                                                  (gensym 'ex))))])
      (eval-type (syntax/loc src-id
                   (Exv uid/q*)))))

  ; compare two syntax objects to see if they are identical exvars
  (define (exv=? e1 e2)
    (syntax-parse (list e1 e2)
      #:literals (quote)
      [((~Exv (quote a)) (~Exv (quote b)))
       (eq? (syntax-e #'a) (syntax-e #'b))]
      [_ #f]))

  (let ([e1 (generate-exv)]
        [e2 (generate-exv)])
    (check-not-false (exv=? e1 e1))
    (check-not-false (exv=? e2 e2))
    (check-false (exv=? e1 e2))
    (check-false (exv=? #'e1 e1)))


  ; substitute τ for a in e, if (exv=? x y)
  ; copied from turnstile's subst because who knows how it works anyways
  (define (exv-subst τ a e)
    (syntax-parse e
      [(~Exv ((~literal quote) uid))
       #:when (exv=? e a)
       (transfer-stx-props τ (merge-type-tags (syntax-track-origin τ e #'uid)))]
      [(esub ...)
       #:with res (stx-map (λ (e1) (exv-subst τ a e1)) #'(esub ...))
       (transfer-stx-props #'res e #:ctx e)]
      [_ e]))

  (let* ([e1 (generate-exv)]
         [e2 (generate-exv)]
         [T  (eval-type #`(→ #,e1 Unit))]
         [T- (eval-type #`(→ #,e2 Unit))])
    (check-equal? (syntax->datum (exv-subst e2 e1 T))
                  (syntax->datum T-)))


  )


;; contexts
(begin-for-syntax
  ;; a context is a (listof ctx-elem)
  ;; a ctx-elem is one of
  ;;   (list ': id ty)       ; x : T
  ;;   (list '= exv ty)      ; a = T
  ;;   (list '▹ exv)         ; ▹ a
  ;;   (list 'e exv)         ; a
  ;;   (list 'v id)          ; X

  ; specializes equality for identifiers (bound-identifier=?) and exvars (Exvar=?)
  (define (exv/id=? a b)
    (cond
      [(and (identifier? a) (identifier? b))
       (bound-identifier=? a b)]
      [(and (Exv? a) (Exv? b))
       (exv=? a b)]
      [else
       (equal? a b)]))


  ; split a context in half by the specified key and second elem
  ; returns a list of both halfs
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
  ; returns a list of all the subcontexts
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
        [e3 (generate-exv)]
        [x #'x] [y #'y])
    (check-equal? (ctx-split (list (list '▹ e1)
                                   (list ': x e2)
                                   (list 'e (eval-type e2))
                                   (list ': y e3)
                                   (list '▹ e3))
                             'e e2
                             ': y)
                  (list (list (list '▹ e1)
                              (list ': x e2))
                        (list)
                        (list (list '▹ e3)))))


  ; apply substitutions in a context to a type
  (define (ctx-subst ctx T)
    (match ctx
      ['() T]
      [(cons (list '= a A) ctx2)
       (ctx-subst ctx2 (exv-subst A a T))]
      [(cons _ ctx2)
       (ctx-subst ctx2 T)]))

  (let* ([e1 (generate-exv)]
         [e2 (generate-exv)]
         [e3 (generate-exv)]
         [ctx (list (list ': #'x e1)
                    (list 'e e3)
                    (list '▹ e3)
                    (list '= e2 e1)
                    (list '▹ e2)
                    (list '= e1 (eval-type #'Unit))
                    (list '▹ e1))]
         [T  (eval-type #`(→ #,e1 (→ #,e2 #,e3)))]
         [T- (eval-type #`(→ Unit (→ Unit #,e3)))])
    (check-equal? (syntax->datum (ctx-subst ctx T))
                  (syntax->datum T-)))

  ; predicates for search contexts
  (define (ctx-contains-var? ctx X)
    (memf (match-lambda
            [(list 'v Y) (bound-identifier=? X Y)]
            [_ #f])
          ctx))
  (define (ctx-contains-exv? ctx e)
    (memf (match-lambda
            [(list 'e e2) (exv=? e e2)]
            [_ #f])
          ctx))

  ; well-formedness check
  (define (well-formed? ctx T)
    (syntax-parse T
      [~Unit #t]
      [(~→ T1 T2)
       (and (well-formed? ctx #'T1)
            (well-formed? ctx #'T2))]
      [(~∀ (X) T1)
       (well-formed? (cons (list 'v #'X) ctx)
                     #'T1)]
      [_:id
       (ctx-contains-var? ctx T)]
      [(~Exv _)
       (ctx-contains-exv? ctx T)]))

  (let* ([e1 (generate-exv)]
         [e2 (generate-exv)]
         [ctx (list (list 'e e1))]
         [T (eval-type #'(∀ (X) (→ X Unit)))])
    (check-not-false (well-formed? ctx e1))
    (check-false (well-formed? ctx e2))
    (check-not-false (well-formed? ctx T))
    (syntax-parse T
      [(~∀ (_) T-) (check-false (well-formed? ctx #'T-))]))



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
