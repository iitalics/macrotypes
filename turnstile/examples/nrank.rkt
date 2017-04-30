#lang racket
(require turnstile
         (for-syntax racket
                     rackunit))

; fundamental types
(define-base-types Unit Int Nat)
(define-type-constructor → #:arity = 2)
(define-binding-type All #:bvs = 1 #:arity = 1)

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


  ; a ContextElem (ctx-elem) is one of:
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
  (define (ctx-prepend! ces [ctx (current-ctx)])
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
  (define (ctx-subst T [ctx (current-ctx)])
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
    (check-equal? (syntax->datum (ctx-subst T1
                                            (mk-ctx* (ctx-mark)
                                                     (e2 . ctx-ev= . e1)
                                                     (ctx-ev e2)
                                                     (e1 . ctx-ev= . Int))))
                  (syntax->datum T2)))


  ; is the given type well formed under the context?
  (define (well-formed? t [ctx (current-ctx)])
    (syntax-parse t
      [a:id
       (ctx-find (ctx-tv/c #'a) ctx)]
      [(~and e (~Evar _))
       (ctx-find (match-lambda
                   [(ctx-ev e2) (Evar=? #'e e2)]
                   [(ctx-ev= e2 _) (Evar=? #'e e2)]
                   [_ #f])
                 ctx)]
      [(~→ A B)
       (and (well-formed? #'A ctx)
            (well-formed? #'B ctx))]
      [(~All (X) T)
       (well-formed? #'T (ctx-cons (ctx-tv #'X) ctx))]
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



  )
