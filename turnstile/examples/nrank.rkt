#lang turnstile/lang
(require "nrank-evar.rkt"
         (for-syntax racket
                     "nrank-context.rkt"))

(provide (for-syntax monotype?
                     well-formed?
                     inst-evar
                     subtype))

; fundamental types
(define-base-types Unit Num Int Nat)
(define-type-constructor → #:arity = 2)
(define-binding-type All #:arity = 1 #:bvs = 1)

(begin-for-syntax
  ; string representation of the given type
  (define (type->string t)
    (syntax-parse t
      [~Unit "Unit"]
      [~Nat "Nat"]
      [~Int "Int"]
      [~Num "Num"]
      [(~→ T1 T2) (format "(→ ~a ~a)"
                          (type->string #'T1)
                          (type->string #'T2))]
      [(~All (X) T) (format "(∀ (~a) ~a)"
                            (syntax-e #'X)
                            (type->string #'T))]
      [(~Evar ((~literal quote) s)) (format "{~a}"
                                            (syntax-e #'s))]
      [x:id (symbol->string (syntax-e #'x))]))


  ; a monotype is a type without quantifications (foralls)
  (define (monotype? t)
    (syntax-parse t
      [(~All (X) _) #f]
      [(~→ T1 T2) (and (monotype? #'T1)
                       (monotype? #'T2))]
      [_ #t]))


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
      [_ #t]))


  ; instantiation algorithm. instantiate evar 'e' to be type 't' under
  ; the given context, in the given direction. returns #t if succeeds,
  ; #f if fails to instantiate.
  ; e <: t   if dir is '<:
  ; t <: e   if dir is ':>
  (define (inst-evar e dir t [ctx (current-ctx)])
    (syntax-parse t
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
              [mrk (ctx-mark (format "▹~a" (syntax-e #'X)))])
         (ctx-cons! mrk ctx)
         (ctx-cons! (ctx-ev ex) ctx)
         (begin0 (inst-evar e dir (subst ex #'X #'B))
           (ctx-pop-until! (ctx-mark/c mrk) ctx)))]

      ; rule: Inst[L/R]Solve
      [τ #:when (and (monotype? #'τ)
                     (well-formed?/list #'τ (get-before ctx (ctx-ev/c e))))
         (ctx-call-between ctx (ctx-ev/c e)
                           (lambda ()
                             (ctx-cons! (e . ctx-ev= . #'τ) ctx)
                             #t))]

      ; rule: Inst[L/R]Reach
      [(~and e2 (~Evar _))
       (and (memf (ctx-ev/c #'e2)
                  (get-after ctx (ctx-ev/c e)))
            (ctx-call-between ctx (ctx-ev/c #'e2)
                              (lambda ()
                                (ctx-cons! (#'e2 . ctx-ev= . e) ctx)
                                #t)))]

      ; rule: Inst[L/R]Arr
      [(~→ A1 A2)
       (let* ([tmp (unbox ctx)]
              [e1 (mk-evar e)]
              [e2 (mk-evar e)]
              [e1->e2 ((current-type-eval) #`(→ #,e1 #,e2))]
              [dir- (case dir [(<:) ':>] [(:>) '<:])])
         (ctx-call-between ctx (ctx-ev/c e)
                           (lambda ()
                             (ctx-cons! (ctx-ev e2) ctx)
                             (ctx-cons! (ctx-ev e1) ctx)
                             (ctx-cons! (e . ctx-ev= . e1->e2) ctx)))
         (or (and (inst-evar e1 dir- #'A1)
                  (inst-evar e2 dir  (subst-from-ctx #'A2 ctx)))
             (begin (set-box! ctx tmp)
                    #f)))]

      [_ #f]))


  ; subtype algorithm. returns #t and modifies the context
  ; if t1 can be made to subtype t2 (t1 <: t2). returns #f
  ; otherwise
  (define (subtype t1 t2 [ctx (current-ctx)])
    (syntax-parse (list t1 t2)
      [(x y)
       #:when (type=? #'x #'y)
       #t]

      ; rule: <:Unit (plus some new types)
      [(~or (~Nat  ~Int)
            (~Int  ~Num)
            (~Nat  ~Num))
       #t]

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
       (let ([mrk (ctx-mark (format "▹~a" (syntax-e #'X)))]
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

      [_ #f]))


  ; typecheck that the expression has the given type
  ; returns a syntax list with the first element containing all of the
  ; expanded forms of variables, and the second element containing the
  ; expanded expression
  (define (tycheck expr t
                   [x:ts '()]
                   #:before [before-fn void]
                   #:after [after-fn void])
    (syntax-parse t
      ; rule: ∀I
      [(~All (X) T)
       #:do [(ctx-cons! (ctx-tv #'X))]
       #:with ((x- ...) expr-) (tycheck expr #'T x:ts
                                        #:before before-fn
                                        #:after after-fn)
       #:do [(ctx-pop-until! (ctx-tv/c #'X))]
       #'((x- ...) expr-)]

      [T ; do typechecking
       #:with ([x τ] ...) x:ts
       #:do [(before-fn)]
       #:and (~typecheck [[x ≫ x- : τ] ... ⊢ #,expr ≫ expr- ⇐ T])
       #:do [(after-fn)]
       #'((x- ...) expr-)]))


  ; override the typecheck relation to use contexts
  [current-typecheck-relation
   (λ (t1 t2)
     (cond
       ; for some reason turnstile keeps calling this with identical arguments
       [(eq? t1 t2) #t]
       [else
        ; rule: Sub
        (let* ([t1- (subst-from-ctx t1)]
               [t2- (subst-from-ctx t2)])
          (subtype t1- t2-))]))]


  ; apply a function of the given type to the given expression, synthesizing
  ; the resulting type. returns a syntax list with the first element containing
  ; the result type and the second element containig the expanded form of the argument.
  (define (app⇒⇒ t arg #:src [src arg])
    (syntax-parse t
      ; rule: ∀App
      [(~All (X) A)
       (let ([ex (mk-evar #'X)])
         (ctx-cons! (ctx-ev ex))
         (app⇒⇒ (subst ex #'X #'A) arg #:src src))]

      ; rule: →App
      [(~→ A C)
       #:with (() arg-) (tycheck arg #'A)
       #'(C arg-)]

      ; rule: αApp
      [(~and e (~Evar _))
       #:with e1 (mk-evar #'arg)
       #:with e2 (mk-evar #'ret)
       #:with e1->e2 ((current-type-eval) #'(→ e1 e2))
       #:do [(ctx-call-between (current-ctx) (ctx-ev/c #'e)
                           (lambda _
                             (ctx-cons! (ctx-ev #'e2))
                             (ctx-cons! (ctx-ev #'e1))
                             (ctx-cons! (#'e . ctx-ev= . #'e1->e2))))]
       #:with (() arg-) (tycheck arg #'e1)
       #'(e2 arg-)]

      [_
       (raise-syntax-error #f (format "cannot apply non-function type: ~a"
                                      (type->string t))
                           src)]))

  )


(define- +/curry (lambda (x) (lambda (y) (#%app- + x y))))

(provide #%app #%datum lambda define
         define-type-alias
         (rename-out [lambda λ])
         ann typeof
         (type-out All → Nat Int Num Unit)
         (typed-out [[add1 (→ Nat Nat)] succ]
                    [[add1 (→ Int Int)] add1]
                    [[add1 (→ Num Num)] 1+]
                    [[values (All (X) (→ X X))] id]
                    [[+/curry (→ Num (→ Num Num))] +]
                    ))

; prints the type of an expression
(define-typed-syntax typeof
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ T]
   #:with s (type->string (subst-from-ctx #'T))
   --------
   [⊢ (#%app- displayln 's) ⇒ Unit]])


(define-typed-syntax ann
  ; rule: Anno
  [(_ e (~datum :) hint:type) ≫
   #:with T #'hint.norm
   #:with (() e-) (tycheck #'e #'T)
   --------
   [⊢ e- ⇒ T]])

(define-typed-syntax #%app
  ;; sugary ann syntax
  [{_ e (~datum :) hint} ≫
   #:when (equal? #\{ (syntax-property this-syntax 'paren-shape))
   --------
   [≻ (ann e : hint)]]

  ;; unit syntax
  ; rule: 1I
  [(_) ⇐ u ≫
   #:when (Unit? #'u)
   --------
   [⊢ '()]]

  ; rule: 1I⇒
  [(_) ≫
   --------
   [⊢ '() ⇒ Unit]]

  ;; application syntax
  ; rule: →E
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ A]
   #:with (C e2-) (app⇒⇒ (subst-from-ctx #'A) #'e2 #:src #'e1)
   --------
   [⊢ (#%app- e1- e2-) ⇒ C]]

  ;; sugary application syntax
  [(_ e1 e2 ... e3) ≫
   --------
   [≻ (#%app (#%app e1 e2 ...) e3)]])

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
   #:with ((x-) body-)
   (let ([mrk (ctx-mark (format "~a : ~a"
                                (syntax-e #'x)
                                (type->string #'τ1)))])
     (tycheck #'body #'τ2 #'([x τ1])
              #:before (lambda () (ctx-cons! mrk))
              #:after  (lambda () (ctx-pop-until! (ctx-mark/c mrk)))))
   --------
   [⊢ (lambda- (x-) body-)]]

  [(_ (x) body) ⇐ τ ≫
   #:when (not (Evar? #'τ))
   #:with (~!) '()
   --------
   [#:error (format "unexpected function; expected type ~a"
                    (type->string #'τ))]]

  ; rule: →I⇒
  [(_ (x) body) ≫
   #:with e1 (mk-evar #'x)
   #:with e2 (mk-evar)
   #:with ((x-) body-)
   (let* ([mrk (ctx-mark (format "~a : ~a" (syntax-e #'x) (type->string #'e1)))])
     (tycheck #'body #'e2 #'([x e1])
              #:before (lambda ()
                         (ctx-cons! (ctx-ev #'e1))
                         (ctx-cons! (ctx-ev #'e2))
                         (ctx-cons! mrk))
              #:after (lambda ()
                        (ctx-pop-until! (ctx-mark/c mrk)))))
   --------
   [⊢ (lambda- (x-) body-) ⇒ (→ e1 e2)]]

  [(_ (x y ...) body) ≫
   --------
   [≻ (lambda (x) (lambda (y ...) body))]])


(define-syntax define
  (syntax-parser
    [(_ (f:id [x:id (~datum :) x-ty] ...) (~datum :) ret-ty body)
     #'(typed-define f : (→ x-ty ... ret-ty)
                     (lambda (x ...) body))]

    [(_ x:id (~datum :) t:type body)
     #:with T #'t.norm
     #:with y (generate-temporary #'x)
     #'(begin-
         (define-syntax x (make-rename-transformer (⊢ y : T)))
         (define- y (ann body : T)))]))

;; τ.norm in 1st case causes "not valid type" error when file is compiled
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]
    [(_ (f:id x:id ...) ty)
     #'(define-syntax- (f stx)
         (syntax-parse stx
           [(_ x ...)
            #:with τ:any-type #'ty
            #'τ.norm]))]))


(define-for-syntax (display-ctx ctx [mrk #f])
  (for ([ce (in-list (unbox ctx))])
    (match ce
      [(ctx-ev e)    (printf "ev: ~a\n" (type->string e))]
      [(ctx-ev= e t) (printf "ev: ~a = ~a\n" (type->string e) (type->string t))]
      [(ctx-tv v)    (printf "tv: ~a\n" (syntax-e v))]
      [(ctx-mark d)  (if (eq? ce mrk)
                         (printf "*mark ~a\n" d)
                         (printf "mark ~a\n" d))]))
  (printf ";\n"))

(provide print-ctx reset-ctx)

(define-typed-syntax print-ctx
  [_ ≫
   #:do [(display-ctx (current-ctx))]
   --------
   [⊢ (#%app- void) ⇒ Unit]])

(define-typed-syntax reset-ctx
  [_ ≫
   #:do [(set-box! (current-ctx) '())]
   ---------
   [⊢ (#%app- void) ⇒ Unit]])
