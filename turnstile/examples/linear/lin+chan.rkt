#lang turnstile/lang
(extends "lin+tup.rkt")

(provide (type-out InChan OutChan)
         make-channel channel-put channel-get
         thread sleep)

(define-type-constructor InChan #:arity = 1)
(define-type-constructor OutChan #:arity = 1)

(begin-for-syntax
  [current-linear? (or/c InChan? [current-linear?])])


(define-typed-syntax make-channel
  [(_ {ty:type}) ≫
   #:with σ #'ty.norm
   #:with tmp (generate-temporary)
   --------
   [⊢ (let- ([tmp (#%app- make-channel-)])
            (#%app- list- tmp tmp))
      ⇒ (⊗ (InChan σ) (OutChan σ))]])


(define-typed-syntax channel-put
  [(_ ch e) ≫
   [⊢ ch ≫ ch- ⇒ (~OutChan σ)]
   [⊢ e ≫ e- ⇐ σ]
   --------
   [⊢ (#%app- channel-put- ch- e-) ⇒ Unit]])


(define-typed-syntax channel-get
  [(_ ch) ≫
   [⊢ ch ≫ ch- ⇒ (~InChan σ)]
   #:with tmp (generate-temporary #'ch)
   --------
   [⊢ (let- ([tmp ch-])
            (#%app- list- tmp (#%app- channel-get- tmp)))
      ⇒ (⊗ (InChan σ) σ)]])


(define-typed-syntax thread
  [(_ f) ≫
   [⊢ f ≫ f- ⇒ (~-o _)]
   --------
   [⊢ (#%app- void- (#%app- thread- f-)) ⇒ Unit]])


(define-typed-syntax sleep
  [(_) ≫
   --------
   [⊢ (#%app- sleep-) ⇒ Unit]]

  [(_ e) ≫
   [⊢ e ≫ e- ⇒ σ]
   #:fail-unless (or (Int? #'σ)
                     (Float? #'σ))
   "invalid sleep time, expected Int or Float"
   --------
   [⊢ (#%app- sleep- e-) ⇒ Unit]])
