#lang turnstile/lang
(extends "lin+tup.rkt")

(provide (type-out LList LList0)
         cons nil match-list)

(define-type-constructor LList #:arity = 1)
(define-base-type LList0)

(begin-for-syntax
  (define (fail/unbalanced-branches x)
    (raise-syntax-error #f "linear variable may be unused in certain branches" x))

  [current-linear? (or/c LList? LList0? [current-linear?])])

(define-typed-syntax cons
  #:datum-literals (@)

  ; implicit memory location created
  [(_ e e_rest) ≫
   [⊢ e ≫ e- ⇒ σ]
   [⊢ e_rest ≫ e_rest- ⇐ (LList σ)]
   --------
   [⊢ (#%app- mcons- e- e_rest-) ⇒ (LList σ)]]

  ; with memory location given
  [(_ e e_rest @ e_loc) ≫
   [⊢ e ≫ e- ⇒ σ]
   [⊢ e_rest ≫ e_rest- ⇐ (LList σ)]
   [⊢ e_loc ≫ e_loc- ⇐ LList0]
   #:with tmp (generate-temporary #'e_loc)
   --------
   [⊢ (let- ([tmp e_loc-])
            (#%app- set-mcar!- tmp e-)
            (#%app- set-mcdr!- tmp e_rest-)
            tmp)
      ⇒ (LList σ)]])

(define-typed-syntax nil
  [(_) ⇐ (~LList σ) ≫
   --------
   [⊢ '()]])

(define-typed-syntax match-list
  #:datum-literals (cons nil @ ->)
  [(_ e_list
      (~or (~seq (cons x+:id xs+:id @ l+:id) -> e_cons+)
           (~seq nil -> e_nil+)) ...) ≫
   #:with [(l x xs e_cons)] #'[(l+ x+ xs+ e_cons+) ...]
   #:with [e_nil] #'[e_nil+ ...]

   ; list
   [⊢ e_list ≫ e_list- ⇒ (~LList σ)]
   #:do [(define scope-pre-branch linear-scope)]

   #:with llst ((current-type-eval) #'(LList σ))
   #:with llst0 ((current-type-eval) #'LList0)

   ; cons branch
   [[x ≫ x- : σ]
    [xs ≫ xs- : llst]
    [l ≫ l- : llst0]
    ⊢ e_cons ≫ e_cons- ⇒ σ_out]
   #:do [(pop-linear-context! #'([x- σ] [xs- llst] [l- llst0]))]
   #:do [(define scope-cons (swap-linear-scope! scope-pre-branch))]

   ; nil branch
   [⊢ e_nil ≫ e_nil- ⇐ σ_out]
   #:do [(merge-linear-scope! scope-cons
                              #:fail fail/unbalanced-branches)]

   #:with tmp (generate-temporary #'e_list)
   --------
   [⊢ (let- ([tmp e_list-])
            (if- (#%app- null? tmp)
                 e_nil-
                 (let- ([l- tmp]
                        [x- (#%app- mcar- tmp)]
                        [xs- (#%app- mcdr- tmp)])
                       e_cons-)))
      ⇒ σ_out]])
