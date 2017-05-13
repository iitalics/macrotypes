#lang racket
(require macrotypes/typecheck
         (except-in "../../contexty/dunf-krishn.rkt"
                    #;#%app)
         "../../contexty/context.rkt")

(begin-for-syntax
  (require racket/base
           syntax/parse
           rackunit)

  (define-syntax-rule (check-syntax expr patn)
    (syntax-parse expr
      [patn (check-true #t)]
      [_ (fail (format "expected ~a" 'patn))]))

  (define I ((current-type-eval) #'Int))
  (define N ((current-type-eval) #'Nat))
  (define M ((current-type-eval) #'Num))
  (define U ((current-type-eval) #'Unit))


  ; test Exis=? and ~Exis=
  (let ([α (make-exis)]
        [β (make-exis)])
    (check-not-false (Exis=? α α))
    (check-not-false (Exis=? α ((current-type-eval) α)))
    (check-false (Exis=? α β))
    (syntax-parse α
      [(~Exis= β) (fail "matched different exis vars")]
      [(~Exis= α) (check-true #t)]
      [_ (fail "failed to match same exis var")]))


  ; test ctx-subst
  (with-syntax ([α (make-exis)]
                [β (make-exis)])
    ; single substitutions
    (parameterize ([the-context '()])
      (context-push! #'(β . Exis:= . Unit) #'α)
      (check-syntax (ctx-subst #'α) (~Exis= #'α))
      (check-syntax (ctx-subst #'β) ~Unit))
    ; chain substitutions
    (parameterize ([the-context '()])
      (context-push! #'(β . Exis:= . Nat)
                     #'(α . Exis:= . (→ Unit β)))
      (check-syntax (ctx-subst #'α) (~→ ~Unit ~Nat)))
    ; ∀ substitutions
    (parameterize ([the-context '()])
      (define T ((current-type-eval) #'(∀ (X) α)))
      (syntax-parse T
        [(~∀ (X) I)
         (context-push! #`(α . Exis:= . #,(mk-type #'X)))
         (check-syntax (ctx-subst T)
                       (~and (~∀ (Y:id) Z:id)
                             (~do (check bound-identifier=? #'Y #'Z))))])))


  ; test well-formed?
  (let* ([α (make-exis)]
         [α->N ((current-type-eval) #`(→ #,α Nat))]
         [Id ((current-type-eval) #'(∀ (X) (→ X X)))])
    (check-not-false (well-formed? α (list α)))
    (check-false     (well-formed? α (list)))
    (check-false     (well-formed? Id (list)))
    (syntax-parse Id
      [(~∀ (X) τ)
       (check-not-false (well-formed? #'τ (list α #'X)))
       (check-false (well-formed? #'τ (list)))]))


  ; test subtype
  (check-true (subtype I I))
  (check-true (subtype N N))
  (check-true (subtype M M))
  (check-true (subtype N I))
  (check-true (subtype I M))
  (check-true (subtype N M))
  (check-false (subtype N U))
  (check-false (subtype M N))
  (check-true (subtype ((current-type-eval) #`(→ Int Int))
                       ((current-type-eval) #`(→ Nat Num))))
  (check-false (subtype ((current-type-eval) #`(→ Int Int))
                        ((current-type-eval) #`(→ Num Nat))))

  (syntax-parse (list ((current-type-eval) #'(∀ (X) X))
                      ((current-type-eval) #'(∀ (X) X)))
    [((~∀ (_) X) (~∀ (_) Y))
     (check-false (subtype #'X #'Y))
     (check-true (subtype #'X #'X))])

  (check-true (subtype N ((current-type-eval) #'(∀ (X) Int))))
  (check-equal? '() (the-context))

  (with-syntax ([α (make-exis)]
                [β (make-exis)])
    (parameterize ([the-context (list #'α)])
      (check-true (subtype #'α I))
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= #'α) ~Int)})))


  ; test inst-subtype
  (with-syntax ([α (make-exis)]
                [β (make-exis)])
    ; assignment
    (parameterize ([the-context (list #'α #'β)])
      (inst-subtype #'α '<: #'β)
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= #'α) (~Exis= #'β))
                     (~Exis= #'β)}))
    ; always assigns chronologically; note we switch β <: α but resulting context is same
    (parameterize ([the-context (list #'α #'β)])
      (inst-subtype #'β '<: #'α)
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= #'α) (~Exis= #'β))
                     (~Exis= #'β)}))

    ; assignment to → with nested vars in "wrong" order
    (parameterize ([the-context (list #'α #'β)])
      (inst-subtype #'β '<: ((current-type-eval) #'(→ α Int)))
      ; BEFORE:  Γ = b, a
      ; AFTER:   Δ = a2=Int, a1, b=a1->a2, a=a1
      ; note that all assignments are to variables that occur before the assignment
      ; yet the desired relation still holds
      (syntax-parse (the-context)
        [{(~Exis:= (~Exis= #'α) α=)
          (~Exis:= (~Exis= #'β) (~→ β_arg β_ret))
          (~and α1 (~Exis _))
          (~Exis:= (~and α2 (~Exis _)) ~Int)}
         (check-true (Exis=? #'α= #'α1))
         (check-true (Exis=? #'β_arg #'α1))
         (check-true (Exis=? #'β_ret #'α2))]
        [_ (fail "wrong context form")]))

    ; assignment to ∀'s
    (for ([dir '(<:)])
      (parameterize ([the-context (list #'α)])
        (inst-subtype #'α dir ((current-type-eval) #'(∀ (X) Int)))
        (syntax-parse (the-context)
          [{(~Exis:= _ _)}
           (check-true #t)]
          [{(~Exis _)}
           (fail "no assignment done")]
          [{_}
           (fail "something else?")]
          [{}
           (fail "it's gone :o")])))

    (check-exn exn:fail:inst-subtype?
               (lambda ()
                 ; cannot assign variable introduced in subtype
                 (parameterize ([the-context (list #'α)])
                   (inst-subtype #'α '<: ((current-type-eval) #'(∀ (X) X)))))))

  )
