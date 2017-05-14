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

  )
