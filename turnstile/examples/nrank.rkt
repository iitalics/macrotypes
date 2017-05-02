#lang racket
(require turnstile
         (for-syntax racket
                     rackunit))

; fundamental types
(define-base-types Unit Int Nat)
(define-type-constructor → #:arity = 2)
(define-binding-type All #:bvs = 1 #:arity = 1)

(begin-for-syntax
  ; a monotype is a type without quantifications (foralls)
  (define (monotype? t)
    (syntax-parse t
      [(~All (X) _) #f]
      [(~→ T1 T2) (and (monotype? #'T1)
                       (monotype? #'T2))]
      [_ #t]))

  (check-true (monotype? ((current-type-eval) #'Unit)))
  (check-true (monotype? ((current-type-eval) #'(→ Int Nat))))
  (check-false (monotype? ((current-type-eval) #'(→ (All (X) X) Nat))))
  )

; the one "argument" to an Evar is a mk-type'd quoted symbol
; used to differentiate them
(define-type-constructor Evar #:arity = 1)

(begin-for-syntax
  ; generates a new evar
  (define (mk-evar [src #f])
    (define uniq-sym (gensym (syntax-parse src
                               [x:id (syntax-e #'x)]
                               [_ 'E])))
    (with-syntax ([quot-sym (mk-type #`(quote #,uniq-sym))])
      ((current-type-eval) #'(Evar quot-sym))))

  ; returns #t if both types are the same evars
  (define (Evar=? T1 T2)
    (syntax-parse (list T1 T2)
      [((~Evar ((~literal quote) s1))
        (~Evar ((~literal quote) s2)))
       (symbol=? (syntax-e #'s1)
                 (syntax-e #'s2))]
      [_ #f]))

  (let* ([e1 (mk-evar)]
         [e2 (mk-evar)]
         [T ((current-type-eval) #'Unit)])
    (check-false (Evar=? T e1))
    (check-false (Evar=? e2 T))
    (check-false (Evar=? e1 e2))
    (check-not-false (Evar=? e1 e1))
    (check-not-false (Evar=? e1 ((current-type-eval) e1))))

  ; substitute evar e -> U in T
  (define (evar-subst e U T)
    (syntax-parse T
      [(~and e2 (~Evar _))
       #:when (Evar=? e #'e2)
       (transfer-stx-props U (merge-type-tags (syntax-track-origin U T #'evar-subst)))]
      [(tsub ...)
       #:with res (stx-map (λ (T2) (evar-subst e U T2)) #'(tsub ...))
       (transfer-stx-props #'res T #:ctx T)]
      [_ T]))

  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [Un ((current-type-eval) #'Unit)]
         [T1 ((current-type-eval) #`(→ #,e1 Unit))]
         [T2 ((current-type-eval) #`(→ Unit #,e2))]
         [UU ((current-type-eval) #'(→ Unit Unit))])
    (check-equal? (syntax->datum (evar-subst e1 Un T1))
                  (syntax->datum UU))
    (check-equal? (syntax->datum (evar-subst e1 Un T2))
                  (syntax->datum T2)))


  ; a ContextElem (ce) is one of:
  ;  (ctx-tv id)       (identifier? id)
  ;  (ctx-ev ev)       (Evar? ev)
  ;  (ctx-ev= ev ty)   (and (Evar? ev) (type? ty))
  ;  (ctx-mark)

  ; This roughly corresponds to the Γ definition in the paper,
  ; with the difference that the "x:A" and "▹a" forms are condenced
  ; into just (ctx-mark), where eq? is used to find the specific mark

  (struct ctx-tv (id) #:transparent)
  (struct ctx-ev (ev) #:transparent)
  (struct ctx-ev= (ev ty) #:transparent)
  (struct ctx-mark ())

  ; contract for ctx-tv's that contain the same bound identifier
  (define (ctx-tv/c id)
    (match-lambda
      [(ctx-tv id2) (bound-identifier=? id id2)]
      [_ #f]))

  ; contract for ctx-ev's that contain the same Evar
  (define (ctx-ev/c ev)
    (match-lambda
      [(ctx-ev ev2) (Evar=? ev ev2)]
      [_ #f]))

  ; contract for picking specific ctx-mark's
  (define (ctx-mark/c cm)
    (lambda (c) (eq? c cm)))


  ; a Context (ctx) is a (box l/ce) where l/ce is a list of ContextElem's

  ; current computed context
  (define current-ctx (make-parameter (box '())))

  ; context utility functions
  (define (mk-ctx* . lst) (box lst))
  (define (ctx-find p [ctx (current-ctx)])
    (findf p (unbox ctx)))
  (define (ctx-cons ce [ctx (current-ctx)])
    (box (cons ce (unbox ctx))))
  (define (ctx-cons! ce [ctx (current-ctx)])
    (set-box! ctx (cons ce (unbox ctx))))
  (define (ctx-append! ces [ctx (current-ctx)])
    (set-box! ctx (append ces (unbox ctx))))


  ; removes elements from the given context until it finds one that
  ; matches the given predicate (which it removes as well). returns
  ; the list of elements popped, excluding the element that matched
  ; the predicate.
  (define (ctx-pop-until! p [ctx (current-ctx)])
    (let trav ([lst (unbox ctx)] [acc '()])
      (match lst
        ['()
         (set-box! ctx '()) acc]
        [(cons (? p) rst)
         (set-box! ctx rst) (reverse acc)]
        [(cons elem rst)
         (trav rst (cons elem acc))])))

  (let* ([mrk1 (ctx-mark)] [mrk2 (ctx-mark)] [e1 (mk-evar)] [e2 (mk-evar)]
         [ctx (mk-ctx* mrk1
                       (ctx-ev e1)
                       mrk2
                       (ctx-ev e2))])
    (check-equal? (ctx-pop-until! (ctx-mark/c mrk2) ctx)  (list mrk1 (ctx-ev e1)))
    (check-equal? (unbox ctx) (list (ctx-ev e2)))
    (check-equal? (ctx-pop-until! (lambda _ #f) ctx)           (list (ctx-ev e2)))
    (check-equal? (unbox ctx) '()))


  ; applies all ctx-ev= substitutions in the context to the given type.
  (define (subst-from-ctx T [ctx (current-ctx)])
    (let trav ([t T] [lst (unbox ctx)])
      (match lst
        ['() t]
        [(cons (ctx-ev= e u) rst)
         (trav (evar-subst e u t) rst)]
        [(cons _ rst)
         (trav t rst)])))

  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [Int ((current-type-eval) #'Int)]
         [T1 ((current-type-eval) #`(→ #,e1 (→ #,e2 Nat)))]
         [T2 ((current-type-eval) #`(→ Int (→ Int Nat)))])
    (check-equal? (syntax->datum (subst-from-ctx T1
                                                 (mk-ctx* (ctx-mark)
                                                          (e2 . ctx-ev= . e1)
                                                          (ctx-ev e2)
                                                          (e1 . ctx-ev= . Int))))
                  (syntax->datum T2)))


  ; is the given type well formed under the context?
  (define (well-formed? t [ctx (current-ctx)])
    (well-formed?/list t (unbox ctx)))

  ; is the given type well formed under the context? (not a real context,
  ; but rather a list of context elements)
  (define (well-formed?/list t ctxl)
    (syntax-parse t
      [a:id
       (ormap (ctx-tv/c #'a) ctxl)]
      [(~and e (~Evar _))
       (ormap (match-lambda
                [(ctx-ev e2) (Evar=? #'e e2)]
                [(ctx-ev= e2 _) (Evar=? #'e e2)]
                [_ #f])
              ctxl)]
      [(~→ A B)
       (and (well-formed?/list #'A ctxl)
            (well-formed?/list #'B ctxl))]
      [(~All (X) T)
       (well-formed?/list #'T (cons (ctx-tv #'X) ctxl))]
      [(~or ~Unit ~Int ~Nat) #t]
      [_ #f]))

  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [Nat ((current-type-eval) #'Nat)]
         [T1 ((current-type-eval) #`(→ #,e1 Unit))]
         [T2 ((current-type-eval) #`(→ Nat #,e2))])
    (check-not-false (well-formed? T1 (mk-ctx* (ctx-ev e1))))
    (check-false     (well-formed? T2 (mk-ctx* (ctx-ev e1))))
    (check-not-false (well-formed? T2 (mk-ctx* (ctx-ev= e2 Nat))))
    (syntax-parse ((current-type-eval) #'(All (X) (→ X Unit)))
      [(~All (Y) T)
       (check-false     (well-formed? #'T (mk-ctx*)))
       (check-not-false (well-formed? #'T (mk-ctx* (ctx-tv #'Y))))]))


  ; calls fn such that any affects to ctx will be applied
  ; in the space instead of the first found element that
  ; matches predicate 'p'.
  (define (call-between ctx p fn)
    (let-values ([(a b) (splitf-at (unbox ctx)
                                   (negate p))])
      (set-box! ctx (cdr b))
      (begin0 (fn)
        (ctx-append! a ctx))))


  ; instantiation algorithm. instantiate evar 'e' to be type 't' under
  ; the given context, in the given direction. returns #t if succeeds,
  ; #f if fails to instantiate.
  ; e <: t   if dir is '<:
  ; t <: e   if dir is ':>
  (define (inst-evar e dir t [ctx (current-ctx)])

    (define (get-before p) (cdr (dropf (unbox ctx) (negate p))))
    (define (get-after p) (takef (unbox ctx) (negate p)))

    (define dir-inv
      (case dir [(<:) ':>] [(:>) '<:]))

    (syntax-parse t
      ; rule: Inst[L/R]Solve
      [τ #:when (and (monotype? #'τ)
                     (well-formed?/list #'τ (get-before (ctx-ev/c e))))
         (call-between ctx (ctx-ev/c e)
                       (lambda ()
                         (ctx-cons! (e . ctx-ev= . #'τ) ctx)
                         #t))]

      ; rule: Inst[L/R]Reach
      [(~and e2 (~Evar _))
       (and (memf (ctx-ev/c #'e2)
                  (get-after (ctx-ev/c e)))
            (call-between ctx (ctx-ev/c #'e2)
                          (lambda ()
                            (ctx-cons! (#'e2 . ctx-ev= . e) ctx)
                            #t)))]

      ; rule: Inst[L/R]Arr
      [(~→ A1 A2)
       (let* ([tmp (unbox ctx)]
              [e1 (mk-evar)]
              [e2 (mk-evar)]
              [e1->e2 ((current-type-eval) #`(→ #,e1 #,e2))])
         (call-between ctx (ctx-ev/c e)
                       (lambda ()
                         (ctx-cons! (ctx-ev e2) ctx)
                         (ctx-cons! (ctx-ev e1) ctx)
                         (ctx-cons! (e . ctx-ev= . e1->e2) ctx)))
         (or (and (inst-evar e1 dir-inv #'A1)
                  (inst-evar e2 dir     (subst-from-ctx #'A2 ctx)))
             (begin (set-box! ctx tmp) #f)))]

      ; rule: InstLAllR
      [(~All (X) A)
       #:when (eq? dir '<:)
       (ctx-cons! (ctx-tv #'X) ctx)
       (begin0 (inst-evar e dir #'A)
         (set-box! ctx (get-before (ctx-tv/c #'X))))]

      ; rule: InstRAllL
      [(~All (X) B)
       #:when (eq? dir ':>)
       (let* ([ex (mk-evar #'X)]
              [mrk (ctx-mark)])
         (ctx-cons! mrk ctx)
         (ctx-cons! (ctx-ev ex) ctx)
         (begin0 (inst-evar e dir (subst ex #'X #'B))
           (set-box! ctx (get-before (ctx-mark/c mrk)))))]

      [_ #f]))

  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [init-ctx (lambda _ (mk-ctx* (ctx-ev e2) (ctx-ev e1)))]
         [s->d syntax->datum]
         [T1 ((current-type-eval) #`(→ #,e1 Unit))]
         [T2 ((current-type-eval) #`(→ #,e2 Unit))]
         [T3 ((current-type-eval) #`(All (X) X))])
    ; easy to inst because e1 appears before e2
    (parameterize ([current-ctx (init-ctx)])
      (check-not-false (inst-evar e2 '<: T1))
      (check-equal? (unbox (current-ctx))
                    (list (e2 . ctx-ev= . T1)
                          (ctx-ev e1))))
    ; more difficult to inst before e2 appears after e1
    (parameterize ([current-ctx (init-ctx)])
      (check-not-false (inst-evar e1 '<: T2))
      (match (unbox (current-ctx))
        [(list (ctx-ev= t1 t2) (ctx-ev= t3 t4) (ctx-ev e3) (ctx-ev= e4 t5))
         (check-equal? (s->d t1) (s->d e2))
         (check-equal? (s->d t2) (s->d e3))
         (check-equal? (s->d t3) (s->d e1))
         (check-equal? (s->d t4) (s->d ((current-type-eval) #`(→ #,e3 #,e4))))
         (check-equal? (s->d t5) (s->d ((current-type-eval) #'Unit)))]
        [_ (fail "context has wrong form")]))
    ; inst with foralls
    (parameterize ([current-ctx (init-ctx)])
      (check-false (inst-evar e1 '<: T3))
      (check-equal? (unbox (current-ctx))
                    (list (ctx-ev e2) (ctx-ev e1)))
      (check-not-false (inst-evar e1 ':> T3))
      (check-equal? (unbox (current-ctx))
                    (list (ctx-ev e2) (ctx-ev e1)))))


  ; subtype algorithm. returns #t and modifies the context
  ; if t1 can be made to subtype t2 (t1 <: t2). returns #f
  ; otherwise
  (define (subtype t1 t2 [ctx (current-ctx)])
    (syntax-parse (list t1 t2)
      ; rule: <:Unit (plus some new types)
      [(~or (~Unit ~Unit)
            (~Int  ~Int)
            (~Nat  ~Nat)
            (~Nat  ~Int))
       #t]

      ; rule: <:Exvar
      [(~and (e1 e2) ((~Evar _) (~Evar _)))
       #:when (Evar=? #'e1 #'e2)
       #t]

      ; rule: <:-→
      [((~→ A1 A2) (~→ B1 B2))
       (and (subtype #'B1 #'A1 ctx)
            (subtype (subst-from-ctx #'A2 ctx)
                     (subst-from-ctx #'B2 ctx)
                     ctx))]

      [_ #f]))

  (parameterize ([current-ctx (mk-ctx*)])
    (let ([Int ((current-type-eval) #'Int)]
          [Nat ((current-type-eval) #'Nat)]
          [Unit ((current-type-eval) #'Unit)]
          [I->I ((current-type-eval) #'(→ Int Int))]
          [I->N ((current-type-eval) #'(→ Int Nat))]
          [N->I ((current-type-eval) #'(→ Nat Int))])
      ; basic types
      (check-not-false (subtype Int Int))
      (check-not-false (subtype Nat Int))
      (check-false     (subtype Int Nat))
      (check-false     (subtype Int Unit))
      ; function type (variance!)
      (check-not-false (subtype I->I I->I))
      (check-not-false (subtype I->N I->I))
      (check-not-false (subtype I->I N->I))
      (check-false     (subtype N->I I->I))))


  )
