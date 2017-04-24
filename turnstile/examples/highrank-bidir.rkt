#lang racket
(require turnstile
         (for-syntax racket syntax/parse
                     rackunit)
         (for-meta 2 syntax/parse))


(provide (rename-out [mod-begin #%module-begin]
                     [top #%top-interaction])
         (type-out Unit)
         unit
         ann)


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
        [(~Exv ((~literal quote) uid)) `(Exv ,(syntax-e #'uid))]
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


;; subtyping & instantiation algorithms
(begin-for-syntax

  (struct exn:fail:inst exn:fail ())
  (define (raise-fail-inst msg . args)
    (raise (exn:fail:inst (apply format (cons msg args))
                          (current-continuation-marks))))

  (struct exn:fail:subtype exn:fail ())
  (define (raise-fail-subtype msg . args)
    (raise (exn:fail:subtype (apply format (cons msg args))
                             (current-continuation-marks))))


  (define (ctx->string ctx)
    (string-join (map (lambda (elem)
                        (~a (map (lambda (x)
                                   (if (syntax? x)
                                       (type->string x)
                                       (~a x)))
                                 elem)))
                      ctx)
                 " - "))

  ; returns context where exvar a is instantiated such that
  ;  a <: T   (if dir is '<)
  ;  T <: a   (if dir is '>)
  (define (inst/ctx ctx a T #:dir dir)
    #;(printf "inst  ~a  ~a  ~a\n  ~a\n"
            (type->string a)
            dir
            (type->string T)
            (ctx->string ctx))
    (define dir/flip
      (case dir
        [(<) '>]
        [(>) '<]
        [else (error "dir must either '< or '>")]))

    (define-values (ctx/before-a ctx/after-a)
      (match ctx
        [(list after ...
               (list 'e (== a exv=?))
               before ...)
         (values before after)]
        [_ (raise-fail-inst "trying to inst exvar that doesn't exist: ~a"
                            (type->string a))]))

    (syntax-parse T
      ; InstSolve
      [τ
       #:when (and (monotype? #'τ)
                   (well-formed? ctx/before-a #'τ))
       (append ctx/after-a
               (list (list '= a #'τ))
               ctx/before-a)]

      ; InstReach
      [(~and b (~Exv _))
       #:when (ctx-contains-exv? ctx/after-a #'b)
       (match ctx
         [(list ctx/after-b ...
                (list 'e (== #'b exv=?))
                ctx/before-b ...)
          (append ctx/after-b
                  (list (list '= #'b a))
                  ctx/before-b)])]

      ; InstArr
      [(~→ T1 T2)
       (let* ([a1 (generate-exv)]
              [a2 (generate-exv)]
              [ctx- (inst/ctx (append ctx/after-a
                                      (list (list '= a (eval-type #`(→ #,a1 #,a2)))
                                            (list 'e a1)
                                            (list 'e a2))
                                      ctx/before-a)
                              a1 #'T1
                              #:dir dir/flip)])
         (inst/ctx ctx-
                   a2 (ctx-subst ctx- #'T2)
                   #:dir dir))]

      ; InstLAllR
      [(~∀ (X) T1) #:when (symbol=? dir '<)
       (match (inst/ctx (list* (list 'v #'X)
                               ctx)
                        a #'T1
                        #:dir '<)
         [(list ctx/after-X ...
                (list 'v (== #'X bound-identifier=?))
                ctx/before-X ...)
          ctx/before-X]
         [_ (raise-fail-inst "type variable disappeared after sub-inst")])]

      ; InstRAllL
      [(~∀ (X) T1) #:when (symbol=? dir '>)
       (let ([x1 (generate-exv)])
         (match (inst/ctx (list* (list 'e x1)
                                 (list '▹ x1)
                                 ctx)
                          a (subst x1 #'X #'T1)
                          #:dir '>)
           [(list ctx/after-x ...
                  (list '▹ (== x1 eq?))
                  ctx/before-x ...)
            ctx/before-x]))]

      [_ (raise-fail-inst "no matching clause")]))

  (let ([e1 (generate-exv #'A)]
        [e2 (generate-exv #'B)]
        [e3 (generate-exv #'C)]
        [Un (eval-type #'Unit)]
        [Bot (eval-type #'(∀ (X) X))])
    ; simple assignment
    (check-equal? (inst/ctx (list (list 'e e1)
                                  (list 'dummy))
                            e1 Un
                            #:dir '<)
                  (list (list '= e1 Un)
                        (list 'dummy)))
    ; assignment between two exvars
    (check-equal? (inst/ctx (list (list 'e e2)
                                  (list 'dummy 1)
                                  (list 'e e1)
                                  (list 'dummy 2))
                            e1 e2
                            #:dir '<)
                  (list (list '= e2 e1)
                        (list 'dummy 1)
                        (list 'e e1)
                        (list 'dummy 2)))
    (check-equal? (inst/ctx (list (list 'e e2)
                                  (list 'dummy 1)
                                  (list 'e e1)
                                  (list 'dummy 2))
                            e2 e1 ; NOTE: flipped order; still assigns the LATER exv
                            #:dir '<)
                  (list (list '= e2 e1)
                        (list 'dummy 1)
                        (list 'e e1)
                        (list 'dummy 2)))
    ; infinite type
    (check-exn exn:fail:inst?
               (lambda ()
                 (inst/ctx (list (list 'e e2)
                                 (list 'e e1))
                           e1 (eval-type #`(→ #,e1 Unit))
                           #:dir '<)))
    ; foralls can't always be instantiated
    ; e.g. [ (∀ (X) X) <: a ]  is a no-op
    ; but  [ (∀ (X) X) :> a ]  is impossible
    (check-equal? (inst/ctx (list (list 'e e1))
                            e1 Bot
                            #:dir '>)
                  (list (list 'e e1)))
    (check-exn exn:fail:inst?
               (lambda ()
                 (inst/ctx (list (list 'e e1))
                           e1 Bot
                           #:dir '<))))


  ; under input context, if A can be a subtype of B, returns output context
  ; otherwise raises 'subtype-error
  (define (subtype ctx A B)
    #;(printf "subtype  ~a  <:  ~a\n  ~a\n"
            (type->string A)
            (type->string B)
            (ctx->string ctx))
    (syntax-parse (list A B)
      ; Unit
      [(~Unit ~Unit) ctx]

      ; Var
      [(X:id Y:id)
       #:when (bound-identifier=? #'X #'Y)
       #:when (ctx-contains-var? ctx #'X)
       ctx]

      ; Exvar
      [((~Exv _) (~Exv _))
       #:when (exv=? A B)
       #:when (ctx-contains-exv? ctx A)
       ctx]

      ; -→
      [((~→ A1 A2) (~→ B1 B2))
       (let ([ctx2 (subtype ctx #'B1 #'A1)])
         (subtype ctx2
                  (ctx-subst ctx2 #'A2)
                  (ctx-subst ctx2 #'B2)))]

      ; ∀R
      [(A  (~∀ (X) B))
       (match (subtype (list* (list 'v #'X)
                              ctx)
                       #'A #'B)
         [(list ctx/after-X ...
                (list 'v (== #'X bound-identifier=?))
                ctx/before-X ...)
          ctx/before-X])]

      ; ∀L
      [((~∀ (X) A)  B)
       (let ([x (generate-exv #'X)])
         (match (subtype (list* (list 'e x)
                                (list '▹ x)
                                ctx)
                         (subst x #'X #'A)
                         #'B)
           [(list ctx/after-x ...
                  (list '▹ (== x eq?))
                  ctx/before-x ...)
            ctx/before-x]))]

      ; InstantiateL
      [((~Exv _) B)
       #:when (ctx-contains-exv? ctx A)
       (inst/ctx ctx A #'B #:dir '<)]

      ; InstantiateR
      [(A (~Exv _))
       #:when (ctx-contains-exv? ctx B)
       (inst/ctx ctx B #'A #:dir '>)]

      [_ (raise-fail-subtype "incompatible")]))

  (let* ([e1 (generate-exv)]
         [e2 (generate-exv)]
         [Un (eval-type #'Unit)])
    (match (subtype (list (list 'e e1)
                          (list 'dummy))
                    (eval-type #`(→ Unit Unit))
                    (eval-type #`(→ Unit #,e1)))
      [(list (list '= e t)
             (list 'dummy))
       (check-true (exv=? e e1))
       (check-equal? (syntax->datum Un)
                     (syntax->datum t))]
      [_ (fail "output context is wrong")])

    (check-exn exn:fail:inst?
               (lambda ()
                 (subtype (list (list 'e e1))
                          (eval-type #`(∀ (X) (→ X X)))
                          (eval-type #`(∀ (X) (→ X #,e1))))))
    (check-equal? (subtype (list)
                           (eval-type #`(∀ (X) (→ X X)))
                           (eval-type #`(→ Unit Unit)))
                  (list))
    (check-equal? (subtype (list)
                           (eval-type #'(∀ (X) X))
                           (eval-type #'(∀ (Y) Y)))
                  (list)))

  )


;; inference helpers
(begin-for-syntax

  (define (ctx-of s [default '()])
    (or (syntax-property s 'Γ)
        default))

  (define (set-ctx-of s ctx)
    (syntax-property s 'Γ ctx))

  )



(define-syntax mod-begin
  (syntax-parser
    [(_ ...) #'(#%module-begin)]))


(define-typed-syntax top
  [(_ . e) ≫
   [⊢ e ≫ e- ⇒ T]
   #:with T- (ctx-subst (ctx-of #'e-) #'T)
   --------
   [≻ (printf "~a : ~a\n"
              e-
              '#,(type->string #'T-))]])


(define-typed-syntax unit
  [(_) ≫
   --------
   [⊢ '() ⇒ Unit]]

  [(_) ⇐ T ≫
   #:when (Unit? #'T)
   --------
   [⊢ '()]])


(define-typed-syntax ann
  [(_ e (~datum :) t) ≫
   #:with T (eval-type #'t)
   #:with e* (set-ctx-of #'e (ctx-of this-syntax))
   [⊢ e ≫ e- ⇐ T]
   --------
   [⊢ e- ⇒ T]])
