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
       #:and [~⊢ (chk #,e) ≫ e- ⇐ B]
       #'(C e-)]

      [(~and α (~Exis _))
       #:with α2 (make-exis)
       #:with α1 (make-exis)
       #:do [(context-replace! (~Exis= #'α)
                               #'α2
                               #'α1
                               #'(α . Exis:= . (→ α1 α2)))]
       #:and [~⊢ (chk #,e) ≫ e- ⇐ α1]
       #'(α2 e-)]

      [_
       (raise-syntax-error 'application
                           (format "not a function type: ~a"
                                   (type->string A))
                           src)]))

  [current-typecheck-relation
   (lambda (t1 t2)
     (or (eq? t1 t2)
         (subtype (ctx-subst t1)
                  (ctx-subst t2))))]

  )


(provide (type-out Nat Int Num Unit → ∀)
         (rename-out [dat #%datum]
                     [app #%app]
                     [lam lambda]
                     [lam λ])
         ann

         (typed-out [[add1 : (→ Nat Nat)] suc]
                    [[add1 : (→ Int Int)] inc]
                    [[add1 : (→ Num Num)] add1]))


(define-typed-syntax ann
  [(_ e (~datum :) t:type ~!) ≫
   [⊢ (chk e) ≫ e- ⇐ t.norm]
   --------
   [⊢ e- ⇒ t.norm]])



(define-typed-syntax chk
  [(_ e) ⇐ (~∀ (X) T ~!) ≫
   #:with bX (make-bvar #'X)
   #:with T- (subst #'bX #'X #'T)
   #:do [(context-push! #'bX)]
   [⊢ (chk e) ≫ e- ⇐ T-]
   #:do [(context-pop-until! (~bvar= #'bX))]
   --------
   [⊢ e-]]

  [(_ e) ⇐ (~and T_in ~!) ≫
   [⊢ #,(syntax-property #'e 'expected-type #f) ≫ e- ⇒ T_out]
   #:do [(unless (subtype (ctx-subst #'T_out)
                          (ctx-subst #'T_in))
           (raise-syntax-error #f (format "expected type ~a, got ~a"
                                          (type->string (ctx-subst #'T_in))
                                          (type->string (ctx-subst #'T_out)))
                               #'e))]
   --------
   [⊢ e-]]

  [(_ e) ≫
   --------
   [≻ #,(syntax-property #'e 'expected-type #f)]])



(define-typed-syntax dat
  [_ ⇐ (~not #f) ≫ -------- [≻ (chk #,this-syntax)]]

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

  [_ ⇐ (~not #f) ≫ -------- [≻ (chk #,this-syntax)]]

  [(_ (x:id) e ~!) ≫
   #:with α (make-exis)
   #:with β (make-exis)
   #:do [(context-push! #'α #'β #'(Marker α))]
   [[x ≫ x- : α] ⊢ (chk e) ≫ e- ⇐ β]
   #:do [(context-pop-until! (~Marker (~Exis= #'α)))]
   --------
   [⊢ (λ- (x-) e-) ⇒ (→ α β)]])



(define-typed-syntax app
  [_ ⇐ (~not #f) ≫ -------- [≻ (chk #,this-syntax)]]

  [(_) ≫
   --------
   [⊢ '() ⇒ Unit]]

  [(_ f e) ≫
   [⊢ f ≫ f- ⇒ A]
   #:with (C e-) (app⇒⇒ (ctx-subst #'A) #'e #:src this-syntax)
   --------
   [⊢ (#%app- f- e-) ⇒ C]])
