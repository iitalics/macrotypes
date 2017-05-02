#lang turnstile/lang
(require (for-syntax racket
                     rackunit))

; fundamental types
(define-base-types Unit Num Int Nat)
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
  (define (type->string t)
    (syntax-parse t
      [~Unit "1"]
      [~Nat "Nat"]
      [~Int "Int"]
      [~Num "Num"]
      [(~→ T1 T2) (format "(→ ~a ~a)"
                          (type->string #'T1)
                          (type->string #'T2))]
      [(~All (X) T) (format "(∀ (~a) ~a)"
                            (type->string #'X #'T))]
      [(~Evar ((~literal quote) s)) (format "{~a}"
                                            (syntax-e #'s))]))

  ; generates a new evar
  (define (mk-evar [src #f])
    (define uniq-sym (gensym (syntax-parse src
                               [x:id (syntax-e #'x)]
                               [_ 'E])))
    (with-syntax ([quot-sym (mk-type #`(quote #,uniq-sym))])
      ((current-type-eval) #'(Evar quot-sym))))

  ; returns #t if both types are the same evars
  (define (Evar=? t1 t2)
    (syntax-parse (list t1 t2)
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
      [(~→ T1 T2)
       #:with T1- (evar-subst e U #'T1)
       #:with T2- (evar-subst e U #'T2)
       ((current-type-eval) #'(→ T1- T2-))]
      [(~All (X) T1)
       #:with T1- (evar-subst e U #'T1)
       ((current-type-eval) #'(All (X) T1-))]
      [_ T]))

  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [Un ((current-type-eval) #'Unit)]
         [T1 ((current-type-eval) #`(→ #,e1 Unit))]
         [T2 ((current-type-eval) #`(→ Unit #,e2))]
         [U->U ((current-type-eval) #'(→ Unit Unit))])
    (check-equal? (syntax->datum (evar-subst e1 Un T1))
                  (syntax->datum U->U))
    (check-equal? (syntax->datum (evar-subst e1 Un T2))
                  (syntax->datum T2))
    (check-equal? (syntax->datum (evar-subst ((current-type-eval) e2) Un T2))
                  (syntax->datum U->U)))


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

  (define (display-ctx ctx [mrk #f])
    (for ([ce (in-list (unbox ctx))])
      (match ce
        [(ctx-ev e)    (printf "ev: ~a\n" (type->string e))]
        [(ctx-ev= e t) (printf "ev: ~a = ~a\n" (type->string e) (type->string t))]
        [(ctx-tv v)    (printf "tv: ~a\n" (syntax-e v))]
        [(ctx-mark)    (if (eq? ce mrk)
                           (printf "mark*\n")
                           (printf "mark\n"))]))
    (printf ";\n"))


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

  ; get parts of a context before/after the first (latest) element that
  ; maches the given predicate
  (define (get-before ctx p)
    (match (dropf (unbox ctx) (negate p))
      [(cons _ xs) xs]
      [_ '()]))
  (define (get-after ctx p)
    (takef (unbox ctx) (negate p)))


  ; instantiation algorithm. instantiate evar 'e' to be type 't' under
  ; the given context, in the given direction. returns #t if succeeds,
  ; #f if fails to instantiate.
  ; e <: t   if dir is '<:
  ; t <: e   if dir is ':>
  (define (inst-evar e dir t [ctx (current-ctx)])
    (syntax-parse t
      ; rule: Inst[L/R]Solve
      [τ #:when (and (monotype? #'τ)
                     (well-formed?/list #'τ (get-before ctx (ctx-ev/c e))))
         (call-between ctx (ctx-ev/c e)
                       (lambda ()
                         (ctx-cons! (e . ctx-ev= . #'τ) ctx)
                         #t))]

      ; rule: Inst[L/R]Reach
      [(~and e2 (~Evar _))
       (and (memf (ctx-ev/c #'e2)
                  (get-after ctx (ctx-ev/c e)))
            (call-between ctx (ctx-ev/c #'e2)
                          (lambda ()
                            (ctx-cons! (#'e2 . ctx-ev= . e) ctx)
                            #t)))]

      ; rule: Inst[L/R]Arr
      [(~→ A1 A2)
       (let* ([tmp (unbox ctx)]
              [e1 (mk-evar)]
              [e2 (mk-evar)]
              [e1->e2 ((current-type-eval) #`(→ #,e1 #,e2))]
              [dir- (case dir [(<:) ':>] [(:>) '<:])])
         (call-between ctx (ctx-ev/c e)
                       (lambda ()
                         (ctx-cons! (ctx-ev e2) ctx)
                         (ctx-cons! (ctx-ev e1) ctx)
                         (ctx-cons! (e . ctx-ev= . e1->e2) ctx)))
         (or (and (inst-evar e1 dir- #'A1)
                  (inst-evar e2 dir  (subst-from-ctx #'A2 ctx)))
             (begin (set-box! ctx tmp)
                    #f)))]

      ; rule: InstLAllR
      [(~All (X) A)
       #:when (eq? dir '<:)
       (ctx-cons! (ctx-tv #'X) ctx)
       (begin0 (inst-evar e dir #'A)
         (ctx-pop-until! (ctx-tv/c #'X) ctx))]

      ; rule: InstRAllL
      [(~All (X) B)
       #:when (eq? dir ':>)
       (let* ([ex (mk-evar #'X)]
              [mrk (ctx-mark)])
         (ctx-cons! mrk ctx)
         (ctx-cons! (ctx-ev ex) ctx)
         (begin0 (inst-evar e dir (subst ex #'X #'B))
           (ctx-pop-until! (ctx-mark/c mrk) ctx)))]

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
            (~Num  ~Num)

            (~Nat  ~Int)
            (~Int  ~Num)
            (~Nat  ~Num))
       #t]

      ; rule: <:Var
      [(x:id y:id)
       (bound-identifier=? #'x #'y)]

      ; rule: <:Exvar
      [(~and (e1 e2) ((~Evar _) (~Evar _)))
       #:when (Evar=? #'e1 #'e2)
       #t]

      ; rule: <:-→
      [((~→ A1 A2) (~→ B1 B2))
       (let ([tmp (unbox ctx)])
         (or (and (subtype #'B1 #'A1 ctx)
                  (subtype (subst-from-ctx #'A2 ctx)
                           (subst-from-ctx #'B2 ctx)
                           ctx))
             (begin (set-box! ctx tmp) #f)))]

      ; rule: <:∀R
      [(A (~All (X) B))
       (begin
         (ctx-cons! (ctx-tv #'X) ctx)
         (begin0 (subtype #'A #'B ctx)
           (ctx-pop-until! (ctx-tv/c #'X) ctx)))]

      ; rule: <:∀L
      [((~All (X) A) B)
       (let ([mrk (ctx-mark)]
             [ex (mk-evar #'X)])
         (ctx-cons! mrk ctx)
         (ctx-cons! (ctx-ev ex) ctx)
         (begin0 (subtype (subst ex #'X #'A) #'B ctx)
           (ctx-pop-until! (ctx-mark/c mrk) ctx)))]

      ; TODO: occurs check
      ; rule: <:InstantiateL
      [((~and (~Evar _) e) A)
       (inst-evar #'e '<: #'A ctx)]
      ; rule: <:InstantiateR
      [(A (~and (~Evar _) e))
       (inst-evar #'e ':> #'A ctx)]

      [_
       #f]))

  (parameterize ([current-ctx (mk-ctx*)])
    (let ([Int ((current-type-eval) #'Int)]
          [Nat ((current-type-eval) #'Nat)]
          [Unit ((current-type-eval) #'Unit)]
          [I->I ((current-type-eval) #'(→ Int Int))]
          [I->N ((current-type-eval) #'(→ Int Nat))]
          [N->I ((current-type-eval) #'(→ Nat Int))]
          [∀X.X ((current-type-eval) #'(All (X) X))])
      ; basic types
      (check-not-false (subtype Int Int))
      (check-not-false (subtype Nat Int))
      (check-false     (subtype Int Nat))
      (check-false     (subtype Int Unit))
      ; function type (variance!)
      (check-not-false (subtype I->I I->I))
      (check-not-false (subtype I->N I->I))
      (check-not-false (subtype I->I N->I))
      (check-false     (subtype N->I I->I))
      ; foralls
      (check-false     (subtype Int ∀X.X))
      (check-not-false (subtype ∀X.X Int))
      (check-equal? (unbox (current-ctx)) '())
      (check-not-false (subtype Nat ((current-type-eval) #'(All (X) Int))))
      (check-not-false (subtype ∀X.X ((current-type-eval) #'(All (Y) Y))))
      ))

[current-typecheck-relation
 (lambda (t1 t2)
   (let ([r (subtype (subst-from-ctx t1)
                     (subst-from-ctx t2))])
     (printf "~a <: ~a  =>  ~a\n"
             (type->string t1)
             (type->string t2)
             r)
     r))]
)



(provide #%app
         #%datum
         ann
         typeof
         lambda (rename-out [lambda λ])
         (type-out → Nat Int Num Unit)
         )

(define-typed-syntax ann
  [(_ e (~datum :) hint:type) ≫
   #:with T #'hint.norm
   [⊢ e ≫ e- ⇐ T]
   --------
   [⊢ e- ⇒ T]])

(define-typed-syntax typeof
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ T]
   #:with s (type->string (subst-from-ctx #'T))
   --------
   [⊢ (#%app- displayln 's) ⇒ Unit]])

(define-typed-syntax #%app
  ; sugary ann syntax
  [{_ e (~datum :) hint} ≫
   #:when (equal? #\{ (syntax-property this-syntax 'paren-shape))
   --------
   [≻ (ann e : hint)]]

  ; this is actually unit syntax
  ; rule: 1I⇒
  [(_) ≫
   --------
   [⊢ '() ⇒ Unit]])

(define-typed-syntax #%datum
  ; rule: 1I⇒ (extended for other datum)
  [(_ . k:nat) ≫
   -------
   [⊢ 'k ⇒ Nat]]
  [(_ . k:exact-integer) ≫
   --------
   [⊢ 'k ⇒ Int]]
  [(_ . k:number) ≫
   --------
   [⊢ 'k ⇒ Num]]
  [_ ≫
   --------
   [#:error "unsupported datum"]])

(define-typed-syntax lambda
  ; rule: →I
  [(_ (x) body) ⇐ (~→ τ1 τ2) ≫
   #:with (x- body-)
   (let* ([mrk (ctx-mark)]
          [ctx (current-ctx)])
     (ctx-cons! mrk ctx)
     (syntax-parse '()
       [_ #:and (~typecheck [[x ≫ x- : τ1] ⊢ body ≫ body- ⇐ τ2])
          (ctx-pop-until! (ctx-mark/c mrk) ctx)
          #'(x- body-)]))
   --------
   [⊢ (lambda- (x-) body-)]]

  ; rule: →I⇒
  [(_ (x) body) ≫
   #:with e1 (mk-evar #'x)
   #:with e2 (mk-evar #'body)
   #:with (x- body-)
   (let* ([mrk (ctx-mark)]
          [ctx (current-ctx)])
     (ctx-cons! (ctx-ev #'e1) ctx)
     (ctx-cons! (ctx-ev #'e2) ctx)
     (ctx-cons! mrk ctx)
     (syntax-parse '()
       [_ #:and (~typecheck [[x ≫ x- : e1] ⊢ body ≫ body- ⇐ e2])
          (ctx-pop-until! (ctx-mark/c mrk) ctx)
          #'(x- body-)]))
   --------
   [⊢ (lambda- (x-) body-) ⇒ (→ e1 e2)]])
