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
       #:do [(context-push! #'α)]
       (app⇒⇒ (subst #'α #'X #'B) e #:src src)]

      [(~and (~→ B C)
             ~! [~⊢ #,e ≫ e- ⇐ B])
       #'(C e-)]

      [(~and α (~Exis _))
       #:with α2 (make-exis)
       #:with α1 (make-exis)
       #:do [(context-replace! (~Exis= #'α)
                               #'α2
                               #'α1
                               #'(α . Exis:= . (→ α1 α2)))]
       #:with ([~⊢ #,e ≫ e- ⇐ α1]) '()
       #'(α2 e-)]

      [_
       (raise-syntax-error 'application
                           (format "not a function type: ~a"
                                   (type->string A))
                           src)]))

  ; extension: generalization
  ; selects unsolved exis vars appearing after (Marker α_m) in the context. then
  ; generalizes t by surrounding it in ∀'s according to the unsolved variables
  (define (generalize α_m t)
    ; generate generic variable names
    (define var-names '(A B C D E F T1 T2 T3 T4 T5 T6 T7))
    (define (new-var!)
      (let ([name (car var-names)])
        (set! var-names (cdr var-names))
        (syntax-parse ((current-type-eval) #`(∀ (#,name) #,name))
          [(~∀ (_) X) #'X])))
    ; find unsolved
    (define after-ctx (context-after (~Marker (~Exis= α_m))))
    (define unsolved (filter Exis? after-ctx))
    ; replace unsolved with identifiers
    (define ids (reverse (map (lambda (α) (new-var!)) unsolved)))
    (define t+ids
      (ctx-subst t (map (lambda (α id)
                          ((current-type-eval) #`(#,α . Exis:= . #,id)))
                        unsolved
                        ids)))
    ; add foralls
    (begin0
        ((current-type-eval)
         (for/fold ([t- t+ids])
                   ([id (in-list ids)])
           #`(∀ (#,id) #,t-)))
      ; and remove from the real context
      (context-pop-until! (~Marker (~Exis= α_m)))))

  [current-typecheck-relation
   (lambda (t1 t2)
     (or (eq? t1 t2)
         (subtype (ctx-subst t1)
                  (ctx-subst t2))))]

  )


(provide (type-out Nat Int Num Unit ∀ →) →*
         (rename-out [dat #%datum]
                     [app #%app]
                     [lam lambda]
                     [lam λ]
                     [def define])
         ann)

(define-syntax →*
  (syntax-parser
    [(_ a b) #'(→ a b)]
    [(_ a b c ...) #'(→ a (→* b c ...))]))


(define-typed-syntax ann
  [(_ e (~datum :) t:type ~!) ≫
   [⊢ e ≫ e- ⇐ t.norm]
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

  [_ ⇐ (~not #f) ≫
   --------
   [≻ (chk #,this-syntax)]]

  [(_ (x:id) e ~!) ≫
   #:with α (make-exis)
   #:with β (make-exis)
   #:do [(context-push! #'α #'β #'(Marker α))]
   [[x ≫ x- : α] ⊢ e ≫ e- ⇐ β]
   #:do [(context-pop-until! (~Marker (~Exis= #'α)))]
   --------
   [⊢ (λ- (x-) e-) ⇒ (→ α β)]]

  [(_ (x:id y:id ...) e) ≫
   --------
   [≻ (lam (x) (lam (y ...) e))]])



(define-typed-syntax app
  [(_) ≫
   --------
   [⊢ (#%app- void) ⇒ Unit]]

  [(_ f e) ≫
   [⊢ f ≫ f- ⇒ A]
   #:with (C e-) (app⇒⇒ (ctx-subst #'A) #'e #:src this-syntax)
   --------
   [⊢ (#%app- f- e-) ⇒ C]]

  [(_ f e0 e ...) ≫
   --------
   [≻ (app (app f e0) e ...)]])



(define-typed-syntax def
  #:datum-literals (:)

  ; unannotated
  [(_ x:id e) ≫
   #:with α_m (make-exis)
   #:do [(context-push! #'(Marker α_m))]
   [⊢ e ≫ e- ⇒ T]
   #:with T+ (generalize #'α_m (ctx-subst #'T))
   #:do [(context-pop-until! (~Marker (~Exis= #'α_m)))]
   ;
   #:with y (generate-temporary #'x)
   --------
   [⊢ (begin-
        (#%app- printf "defined ~a : ~a\n" 'x '#,(type->string #'T+))
        (define-syntax x (make-rename-transformer (⊢ y : T+)))
        (define- y e-))
      ⇒ Unit]]

  [(_ (f:id x:id ...) e) ≫
   --------
   [≻ (def f (lam (x ...) e))]]


  ; annotated
  [(_ x:id : t:type e) ≫
   [⊢ e ≫ e- ⇐ t.norm]
   #:with y (generate-temporary #'x)
   --------
   [⊢ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : t.norm)))
        (define- y e-))
      ⇒ Unit]]

  [(_ (f:id (x:id : t:type) ...) : r:type e) ≫
   --------
   [≻ (def f : (→* t ... r) (lam (x ...) e))]])




(provide (typed-out [[add1 : (→ Nat Nat)] suc]
                    [[add1 : (→ Int Int)] inc]
                    [[add1 : (→ Num Num)] add1]
                    [[display : (∀ (A) (→ A Unit))] display]
                    [[displayln : (∀ (A) (→ A Unit))] displayln]
                    [[+* : (→* Num Num Num)] +]
                    [[-* : (→* Num Num Num)] -]
                    [[** : (→* Num Num Num)] *]
                    [[/* : (→* Num Num Num)] /]
                    [[expt* : (→* Num Int Num)] expt]
                    [[natrec* : (∀ (A) (→* A (→ A A) (→ Nat A)))] natrec]))


(define (ncurry n f)
  (let aux ([args '()] [n n])
    (if (zero? n)
        (apply f (reverse args))
        (lambda (x) (aux (cons x args) (sub1 n))))))


(define (natrec z s n)
  (if (zero? n) z
      (s (natrec z s (sub1 n)))))

(define natrec* (ncurry 3 natrec))
(define +* (ncurry 2 +))
(define -* (ncurry 2 -))
(define ** (ncurry 2 *))
(define /* (ncurry 2 /))
(define expt* (ncurry 2 expt))
