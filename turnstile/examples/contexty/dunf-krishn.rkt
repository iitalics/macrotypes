#lang racket
(require turnstile
         "context.rkt")

; base types
(define-base-type Unit)
(define-base-type Nat)
(define-base-type Int)
(define-base-type Num)

; function and quantification
(define-type-constructor → #:arity = 2)
(define-binding-type ∀ #:bvs = 1 #:arity = 1)

; existential type
; a (quoted) unique symbol identifier is stored as the first
; argument in order to distinguish the exis var
(define-type-constructor Exis #:arity = 1)


; context elements:
; exis var assignment
(define-type-constructor Exis:= #:arity = 2)
; markers
(define-type-constructor Marker #:arity >= 1)


(provide (type-out Unit Nat Int Num → ∀
                   Exis
                   Exis:=
                   Marker))

(begin-for-syntax
  (require racket/base
           syntax/parse
           (for-syntax syntax/parse))

  (provide make-exis ~Exis= Exis=?
           ctx-subst
           well-formed?
           subtype
           inst-subtype
           (struct-out exn:fail:inst-subtype))


  ; generates a unique new exis var
  (define (make-exis)
    (with-syntax ([qs (mk-type #`(quote #,(gensym)))])
      ((current-type-eval) #'(Exis qs))))


  ; pattern expander that takes an expression and only matches
  ; exis vars that are the same as the given
  (define-syntax ~Exis=
    (pattern-expander
     (syntax-parser
       [(_ exis-expr)
        #:with s1 (generate-temporary #'s)
        #:with s2 (generate-temporary #'s)
        #'(~and (~Exis ((~literal quote) s1))
                (~fail #:unless
                       (syntax-parse exis-expr
                         [(~Exis ((~literal quote) s2))
                          (symbol=? (syntax-e #'s1)
                                    (syntax-e #'s2))]
                         [_ #f])))])))

  ; are the two syntax objects both the same existentials?
  (define (Exis=? α1 α2)
    (syntax-parse α2
      [(~Exis= α1) #t]
      [_ #f]))

  ; pattern expander that matches identifiers that are bound-identifier=? the
  ; given identifier expression
  (define-syntax ~bound-id=
    (pattern-expander
     (syntax-parser
       [(_ id-expr)
        #:with X (generate-temporary #'X)
        #'(~and X:id
                (~fail #:unless (bound-identifier=? #'X id-expr)))])))


  ; apply substitutions from ctx to replace exis vars
  ; according to Exis:= entries in the context
  (define (ctx-subst t [ctx (the-context)])
    (syntax-parse t
      [(~and α (~Exis _))
       (let search ([ctx ctx])
         (cond
           [(null? ctx) t]
           [else
            (syntax-parse (car ctx)
              [((~Exis= #'α) . ~Exis:= . A) (ctx-subst #'A (cdr ctx))]
              [_ (search (cdr ctx))])]))]

      [(~∀ (X) A)
       #:with B (ctx-subst #'A ctx)
       ; TODO: is there a proper way to transfer syntax properties?
       ; maybe a (type-map f τ) function would be helpful
       ((current-type-eval) (syntax/loc t
                              (∀ (X) B)))]

      [(~→ A B)
       #:with A- (ctx-subst #'A ctx)
       #:with B- (ctx-subst #'B ctx)
       ((current-type-eval) (syntax/loc t
                              (→ A- B-)))]

      [_ t]))


  ; checks if the type is a well formed monotype under the context
  ; this is the algorithm [Γ ⊢ τ]
  (define (well-formed? t [ctx (the-context)])
    (syntax-parse t
      [X:id (memf (lambda (y)
                    (and (identifier? y)
                         (bound-identifier=? #'X y)))
                  ctx)]

      [(~→ A B)
       (and (well-formed? #'A ctx)
            (well-formed? #'B ctx))]

      [(~and (~Exis _) α)
       (ormap (syntax-parser
                [(~Exis= #'α) #t]
                [(~Exis:= (~Exis= #'α) _) #t]
                [_ #f])
              ctx)]

      [(~∀ (X) _) #f]
      [_ #t]))


  ; implements the subtyping algorithm [Γ ⊢ A <: B ⊣ Δ] using
  ; global state to handle contexts. returns #t if t1 can be made a subtype of t2
  (define (subtype t1 t2 #:src [src t1])
    (syntax-parse (list t1 t2)
      [(X:id Y:id)
       (bound-identifier=? #'X #'Y)]
      [(A B) #:when (type=? #'A #'B)
       #t]
      [(~or (~Nat  ~Int)
            (~Int  ~Num)
            (~Nat  ~Num))
       #t]
      [((~and (~Exis _) α1) (~Exis= #'α1))
       #t]

      [((~→ A1 A2) (~→ B1 B2))
       (and (subtype #'B1 #'A1)
            (subtype (ctx-subst #'A2)
                     (ctx-subst #'B2)))]

      [(A (~∀ (X) B))
       (context-push! #'X)
       (begin0 (subtype #'A #'B)
         (context-pop-until! (~bound-id= #'X)))]

      ; TODO: occurs?
      [((~and α (~Exis _)) A)
       (inst-subtype #'α '<: #'A #:src src) #t]
      [(A (~and α (~Exis _)))
       (inst-subtype #'α ':> #'A #:src src) #t]

      [_ #f]))


  ; implement the instantiation algorithm [Γ ⊢ α <:= A ⊣ Δ] using
  ; global state to handle contexts. instantiate so that subtyping
  ; is determined by dir, e.g.
  ;   if dir = '<: then α <: t
  ;   if dir = ':> then t <: α
  (define (inst-subtype var dir t #:src [src t])
    (define/with-syntax α var)
    (define dir* (case dir [(<:) ':>] [(:>) '<:]))
    (syntax-parse t
      [τ
       #:when (well-formed? #'τ (context-before (~Exis= #'α)))
       (context-replace! (~Exis= #'α)
                         #'(α . Exis:= . τ))]

      [(~and β (~Exis _))
       #:when (member #'β (context-after (~Exis= #'α)) Exis=?)
       (context-replace! (~Exis= #'β)
                         #'(β . Exis:= . α))]

      [(~→ A1 A2)
       #:with α2 (make-exis)
       #:with α1 (make-exis)
       (context-replace! (~Exis= #'α)
                         #'α2
                         #'α1
                         #'(α . Exis:= . (→ α1 α2)))
       (inst-subtype #'α1 dir* #'A1 #:src src)
       (inst-subtype #'α2 dir (ctx-subst #'A2) #:src src)]

      [(~∀ (X) A) #:when (eq? dir '<:)
       (context-push! #'X)
       (inst-subtype #'α '<: #'A)
       (context-pop-until! (~bound-id= #'X))]

      [(~∀ (X) A) #:when (eq? dir ':>)
       #:with β (make-exis)
       (context-push! #'(Marker β) #'β)
       (inst-subtype #'α ':> (subst #'β #'X #'A))
       (context-pop-until! (~Marker (~Exis= #'β)))]

      [_ (raise-inst-subtype-error var t #:src src)]))

  ; exception to be raised by instantiation failure
  (struct exn:fail:inst-subtype exn:fail:syntax (var rhs))
  (define (raise-inst-subtype-error var rhs #:src src)
    (raise (exn:fail:inst-subtype "cannot instantiate"
                                  (current-continuation-marks)
                                  (list src)
                                  var rhs)))


  (define T ((current-type-eval) #'(∀ (X) X)))
  (define x (syntax-parse T
              [(~∀ (Y) _) #'Y]))

  (displayln (bound-identifier=? x ((current-type-eval)
                                    (syntax-property x 'context-var 'yes!))))

  (syntax-parse ((current-type-eval) #`(Marker #,(syntax-property (mk-type x)
                                                                  'context-var 'yes!)))
    [(~Marker Y)
     (displayln (bound-identifier=? x #'Y))
     (displayln (syntax-property #'Y 'context-var))])

  )
