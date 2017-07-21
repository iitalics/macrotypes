#lang turnstile/lang
(extends "lin+cons.rkt")
(reuse thread sleep #:from "lin+thread.rkt")

(provide (type-out InChan OutChan)
         make-channel channel-put channel-get)

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
