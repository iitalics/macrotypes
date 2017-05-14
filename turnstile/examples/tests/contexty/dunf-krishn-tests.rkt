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


  ;;; test make-bvar, bvar=?, ~bvar= ;;;
  (syntax-parse ((current-type-eval) #'(∀ (ABC) (∀ (ABC) Unit)))
    [(~∀ (X) (~∀ (Y) _))
     #:with x (make-bvar #'X)
     #:with y (make-bvar #'Y)
     (check-false (bound-identifier=? #'x #'y))
     (check-false (bvar=? #'x #'y))
     (syntax-parse ((current-type-eval) #'(→ x y))
       [(~→ x- (~bvar= #'y))
        ; this is the problematic situation:
        (check-false (bound-identifier=? #'x #'x-))
        ; this is the solution:
        (check-true (bvar=? #'x #'x-))
        (check-false (bvar=? #'y #'x-))
        ; we can use these as real vars
        (syntax-parse ((current-type-eval) #'(∀ (x-) x-))
          [(~∀ (Y) Z)
           (check-true (bound-identifier=? #'Y #'Z))])]
       [_ (fail "~bvar= failed")])])


  ;;; test Exis=? and ~Exis= ;;;
  (let ([α (make-exis)]
        [β (make-exis)])
    (check-true (Exis=? α α))
    (check-true (Exis=? α ((current-type-eval) α)))
    (check-false (Exis=? α β))
    (syntax-parse α
      [(~Exis= β) (fail "matched different exis vars")]
      [(~Exis= α) (check-true #t)]
      [_ (fail "failed to match same exis var")]))


  ;;; test ctx-subst ;;;
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
         #:with bX (make-bvar #'X)
         #:with T- (subst #'bX #'X T)
         (context-push! #`(α . Exis:= . bX))
         (check-syntax (ctx-subst #'T-)
                       (~and (~∀ (Y:id) Z:id)
                             (~do (check bound-identifier=? #'Y #'Z))))])))


  ;;; test well-formed? ;;;
  (let* ([α (make-exis)]
         [α->N ((current-type-eval) #`(→ #,α Nat))]
         [Id ((current-type-eval) #'(∀ (X) (→ X X)))])
    (check-true  (well-formed? α (list α)))
    (check-false (well-formed? α (list)))
    (check-false (well-formed? Id (list)))
    (syntax-parse Id
      [(~∀ (X) T)
       #:with bX (make-bvar #'X)
       #:with T- (subst #'bX #'X #'T)
       (check-true (well-formed? #'T- (list α #'bX)))
       (check-false (well-formed? #'T- (list)))]))


  ;;; test subtype ;;;
  (check-true (subtype ((current-type-eval) #'Int)
                       ((current-type-eval) #'Int)))
  (check-true (subtype N I))
  (check-true (subtype I M))
  (check-true (subtype N M))
  (check-false (subtype N U))
  (check-false (subtype M N))
  (check-true (subtype ((current-type-eval) #`(→ Int Int))
                       ((current-type-eval) #`(→ Nat Num))))
  (check-false (subtype ((current-type-eval) #`(→ Int Int))
                        ((current-type-eval) #`(→ Num Nat))))

  ; subtyping with exis vars
  (with-syntax ([α (make-exis)]
                [β (make-exis)])
    (parameterize ([the-context (list #'α)])
      (check-true (subtype #'α I))
      (check-syntax (the-context)
                    {(~Exis:= (~Exis= #'α) ~Int)})))

  ; subtyping with ∀'s that aren't bounded in the body
  (parameterize ([the-context '()])
    ; the marker confirms that the context was returned to normal
    ; without being flushed entirely
    (context-push! #'(Marker Int))
    (check-true (subtype N ((current-type-eval) #'(∀ (X) Int))))
    (check-true (subtype ((current-type-eval) #'(∀ (X) Int)) M))
    (check-syntax (the-context) {(~Marker ~Int)}))

  ; subtyping with ∀'s that ARE bounded
  (check-true (subtype ((current-type-eval) #'(∀ (X) (→ Int X)))
                       ((current-type-eval) #'(→ Int Int))))

  ; α-equivalence
  (check-true (subtype ((current-type-eval) #'(∀ (X) X))
                       ((current-type-eval) #'(∀ (Y) Y))))
  (check-true (subtype ((current-type-eval) #'(∀ (X) (∀ (Y) (→ X Y))))
                       ((current-type-eval) #'(∀ (Y) (∀ (X) (→ X Y))))))


  ;;;; test inst-subtype ;;;
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
    (for ([dir '(<: :>)])
      (parameterize ([the-context (list #'α)])
        (inst-subtype #'α dir ((current-type-eval) #'(∀ (X) Int)))
        (check-syntax (the-context)
                      {(~Exis:= (~Exis= #'α) ~Int)})))

    ; cannot assign α = X since X goes out of scope
    (check-exn exn:fail:inst-subtype?
               (lambda ()
                 (parameterize ([the-context (list #'α)])
                   (inst-subtype #'α '<: ((current-type-eval) #'(∀ (X) X))))))

    ; here, X is made into an exis var, which is assigned to α
    ; and then goes out of scope, leaving the context untouched
    (parameterize ([the-context (list #'α)])
      (inst-subtype #'α ':> ((current-type-eval) #'(∀ (X) X)))
      (check-syntax (the-context) {(~Exis= #'α)})))

  )
