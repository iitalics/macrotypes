#lang turnstile/lang
(extends "lin.rkt")
(provide thread sleep)

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
