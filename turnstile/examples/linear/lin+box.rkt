#lang turnstile/lang
(extends "lin+tup.rkt")

(provide (type-out Box Box0)
         box unbox)

(define-type-constructor Box #:arity = 1)
(define-base-type Box0)

(begin-for-syntax
  [current-linear? (or/c Box? Box0? [current-linear?])])

(define-typed-syntax box
  #:datum-literals (@)
  [(_) ≫
   --------
   [⊢ (box- 'empty) ⇒ Box0]]

  [(_ e) ≫
   [⊢ e ≫ e- ⇒ σ]
   --------
   [⊢ (box- e-) ⇒ (Box σ)]]

  [(_ e @ l) ≫
   [⊢ e ≫ e- ⇒ σ]
   [⊢ l ≫ l- ⇐ Box0]
   #:with v (generate-temporary)
   #:with bx (generate-temporary)
   --------
   [⊢ (let ([v e-] [bx l-])
            (set-box! bx v)
            bx) ⇒ (Box σ)]])

(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Box σ)]
   #:with bx (generate-temporary)
   --------
   [⊢ (let- ([bx e-])
            (list bx (unbox- bx)))
      ⇒ (⊗ Box0 σ)]])
