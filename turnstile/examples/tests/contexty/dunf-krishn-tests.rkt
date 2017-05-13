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
    (void))

  ; test subtype
  (check-true (subtype I I))
  (check-true (subtype N N))
  (check-true (subtype M M))
  (check-true (subtype N I))
  (check-true (subtype I M))
  (check-true (subtype N M))
  (check-false (subtype N U))
  (check-false (subtype M N))
  (check-true (subtype ((current-type-eval) #`(→ #,I #,I))
                       ((current-type-eval) #`(→ #,N #,M))))
  (check-false (subtype ((current-type-eval) #`(→ #,I #,I))
                        ((current-type-eval) #`(→ #,M #,N))))


  ; test well-formed?
  (let* ([α (make-exis)]
         [α->N ((current-type-eval) #`(→ #,α Nat))]
         [Id ((current-type-eval) #'(∀ (X) (→ X X)))])
    (check-not-false (well-formed? α (list α)))
    (check-false     (well-formed? α (list)))

    (check-not-false (well-formed? Id (list)))
    (syntax-parse Id
      [(~∀ (X) τ)
       (check-not-false (well-formed? #'τ (list α #'X)))
       (check-false (well-formed? #'τ (list)))]))


  ; test inst-subtype
  (let* ([α (make-exis)]
         [β (make-exis)])
    ; assignment
    (parameterize ([the-context (list α β)])
      (inst-subtype α '<: β)
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= α) (~Exis= β))
                     (~Exis= β)}))
    ; always assigns chronologically; note we switch β <: α but resulting context is same
    (parameterize ([the-context (list α β)])
      (inst-subtype β '<: α)
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= α) (~Exis= β))
                     (~Exis= β)})))
  )
