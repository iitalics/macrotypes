#lang racket
(require (only-in "../nrank.rkt"
                  → Unit Int Nat Num)
         (for-syntax rackunit
                     "../nrank-context.rkt")
         turnstile
         "../nrank-evar.rkt")

;; Evar tests ;;
(begin-for-syntax
  ; Evar=?
  (let* ([e1 (mk-evar)]
         [e2 (mk-evar)]
         [T ((current-type-eval) #'Unit)])
    (check-false (Evar=? T e1))
    (check-false (Evar=? e2 T))
    (check-false (Evar=? e1 e2))
    (check-not-false (Evar=? e1 e1))
    (check-not-false (Evar=? e1 ((current-type-eval) e1))))

  ; evar-subst
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
  )



;; Context tests ;;
(begin-for-syntax
  ; ctx-pop-until!
  (let* ([mrk1 (ctx-mark 'm1)] [mrk2 (ctx-mark 'm2)] [e1 (mk-evar)] [e2 (mk-evar)]
         [ctx (mk-ctx* mrk1
                       (ctx-ev e1)
                       mrk2
                       (ctx-ev e2))])
    (check-equal? (ctx-pop-until! (ctx-mark/c mrk2) ctx)  (list mrk1 (ctx-ev e1)))
    (check-equal? (unbox ctx) (list (ctx-ev e2)))
    (check-equal? (ctx-pop-until! (lambda _ #f) ctx)           (list (ctx-ev e2)))
    (check-equal? (unbox ctx) '()))

  ; subst-from-ctx
  (let* ([e1 (mk-evar)] [e2 (mk-evar)]
         [Int ((current-type-eval) #'Int)]
         [T1 ((current-type-eval) #`(→ #,e1 (→ #,e2 Nat)))]
         [T2 ((current-type-eval) #`(→ Int (→ Int Nat)))])
    (check-equal? (syntax->datum (subst-from-ctx T1
                                                 (mk-ctx* (ctx-mark 'm1)
                                                          (e2 . ctx-ev= . e1)
                                                          (ctx-ev e2)
                                                          (e1 . ctx-ev= . Int))))
                  (syntax->datum T2)))
  )


;; Algorithm tests ;;
(begin-for-syntax
  ; monotype?
  (check-true (monotype? ((current-type-eval) #'Unit)))
  (check-true (monotype? ((current-type-eval) #'(→ Int Nat))))
  (check-false (monotype? ((current-type-eval) #'(→ (All (X) X) Nat))))


  ; well-formed?
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


  ; inst-evar
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


  ; subtype
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
      (check-equal? (unbox (current-ctx)) '())
      ; complicated foralls
      (check-not-false (subtype ((current-type-eval) #'(All (X) (All (Y) (→ X (→ Y X)))))
                                ((current-type-eval) #'(All (X) (All (Y) (→ X (→ Y X)))))))
      ))


  )
