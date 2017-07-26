#lang turnstile/lang
(extends "lin.rkt")
(reuse ⊗ tup let* #:from "lin+tup.rkt")
(reuse ⊕ var match #:from "lin+var.rkt")
(require (only-in "lin+tup.rkt" ⊗ ~⊗))

(provide (type-out Ptr Clr)
         with-ptr deref
         proj fst snd)

(define-internal-type-constructor Ptr/i)
(define-internal-type-constructor Clr/i)

(define-syntax Ptr
  (syntax-parser
    #:datum-literals (@)
    [(_ τ @ x ...)
     (add-orig (mk-type #'(Ptr/i- τ '(x ...)))
               this-syntax)]))

(define-syntax Clr
  (syntax-parser
    #:datum-literals (@)
    [(_ τ @ x ...)
     (add-orig (mk-type #'(Clr/i τ '(x ...)))
               this-syntax)]))

(begin-for-syntax
  (require syntax/id-set
           syntax/id-table)

  (define Ptr? Ptr/i?)
  (define Clr? Clr/i?)

  (define-syntax ~Ptr
    (pattern-expander
     (λ (stx)
       (syntax-case stx (@)
         [(_ p @ . pxs)
          #'(~Ptr/i p ((~literal quote) pxs))]))))

  (define-syntax ~Clr
    (pattern-expander
     (λ (stx)
       (syntax-case stx (@)
         [(_ p @ . pxs)
          #'(~Clr/i p ((~literal quote) pxs))]))))

  (define borrowed-vars
    (make-parameter (make-immutable-free-id-table)))

  (define borrow-scopes
    (make-parameter '()))

  )


(define-typed-variable-syntax
  #:datum-literals (:)
  [(_ x : σ) ≫
   #:do [(when (and (linear-type? #'σ)
                    (dict-has-key? (borrowed-vars) #'x))
           (raise-syntax-error
            #f (format (string-append "variable cannot be used while borrowed\n"
                                      "  borrowed by: ~a")
                       (syntax-e (dict-ref (borrowed-vars) #'x)))
            #'x))]
   --------
   [≻ (lin:#%lin-var x : σ)]])

(define-typed-syntax with-ptr
  [(_ p @ x e ...+) ≫
   [⊢ x ≫ x- ⇒ σ]
   #:fail-unless (linear-type? #'σ)
   (format "can't borrow unrestricted type ~a" (type->str #'σ))

   #:mode borrowed-vars (dict-set (borrowed-vars) #'x- #'p)
     ([[p ≫ p- : (Ptr σ @ x-)] ⊢ (lin:begin e ...) ≫ e- ⇒ σ_out]
      ; TODO: check references to x- in σ_out
      #:do [(set-remove! (linear-scope) #'x-)])

   --------
   [⊢ (let ([p- x-]) e-) ⇒ σ_out]])


(define-typed-syntax deref
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Ptr σ @ _ ...)]
   #:fail-when (linear-type? #'σ)
   (format "can only deref unrestricted types, given ~a" (type->str #'σ))
   --------
   [⊢ e- ⇒ σ]])


(define-typed-syntax proj
  [(_ e n:nat) ≫
   [⊢ e ≫ e- ⇒ (~Ptr (~⊗ σ ...) @ r ...)]
   #:fail-unless (< (syntax-e #'n) (stx-length #'[σ ...])) "index too large"
   #:with σ_n (list-ref (stx->list #'[σ ...]) (syntax-e #'n))
   --------
   [⊢ (list-ref- e- 'n) ⇒ (Ptr σ_n @ r ...)]])


(define-syntax-rule (fst e) (proj e 0))
(define-syntax-rule (snd e) (proj e 1))
