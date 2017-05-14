#lang turnstile/lang
(require "context.rkt"
         "dunf-krishn.rkt")

(begin-for-syntax

  (define type->string type->str)

  ; apply expression 'e' to function of type 'A'
  ; returns a two-element syntax list; the first element is the
  ; resulting type, the second element is the expanded version of e
  ; e.g.  (app⇒⇒ #'(→ A B) e) = #'(B e-)
  (define (app⇒⇒ A e #:src src)
    (syntax-parse A
      [(~∀ (X) B)
       #:with α (make-exis)
       (app⇒⇒ (subst #'α #'X #'B) e #:src src)]

      [(~→ B C)
       #:and [~⊢ e ≫ e- ⇐ B]
       #'(C e-)]

      [(~and α (~Exis _))
       #:with α2 (make-exis)
       #:with α1 (make-exis)
       #:do [(context-replace! (~Exis= #'α)
                               #'α2
                               #'α1
                               #'(α . Exis:= . (→ α1 α2)))]
       #:and [~⊢ e ≫ e- ⇐ α1]
       #'(α2 e-)]

      [_
       (raise-syntax-error 'application
                           (format "not a function type: ~a"
                                   (type->string A))
                           src)]))


  [current-typecheck-relation
   (lambda (t1 t2)
     (subtype (ctx-subst t1)
              (ctx-subst t2)))]

  )


(provide (type-out Nat Int Num Unit → ∀)
         (rename-out [dat #%datum]
                     [lam lambda]
                     [lam λ]))



(define-typed-syntax dat
  [(_ . k:nat) ≫
   --------
   [⊢ (#%datum- . k) ⇒ Nat]]
  [(_ . k:exact-integer) ≫
   --------
   [⊢ (#%datum- . k) ⇒ Int]]
  [(_ . k:number) ≫
   --------
   [⊢ (#%datum- . k) ⇒ Num]])



(define-typed-syntax lam
  [(_ (x:id) e) ⇐ (~→ A B ~!) ≫
   [[x ≫ x- : A] ⊢ e ≫ e- ⇐ B]
   --------
   [⊢ (λ- (x-) e-)]]

  [(_ (x:id) e) ≫
   #:with α (make-exis)
   #:with β (make-exis)
   #:do [(context-push! #'α #'β #'(Marker α))]
   [[x ≫ x- : α] ⊢ e ≫ e- ⇐ β]
   #:do [(context-pop-until! (~Marker (~Exis= #'α)))]
   --------
   [⊢ (λ- (x-) e-) ⇒ (→ α β)]]

  [_ ≫
   #:fail-when #t ":("
   --------
   [≻ ()]])
