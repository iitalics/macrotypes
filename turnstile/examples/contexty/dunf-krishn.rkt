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

  (provide make-bvar ~bvar= bvar=?
           make-exis ~Exis= Exis=?
           ctx-subst
           well-formed?
           subtype
           inst-subtype
           (struct-out exn:fail:inst-subtype))


  ;;; this bvar stuff is used because I need to be able to keep track of identifiers
  ;;; bound in (∀ (X) ...), but when you (current-type-eval) an identifier, it sometimes
  ;;; loses its scope and no longer bound-identifier=? with the original. so we want the
  ;;; property of bound-identifier=? in that it can discriminate identifiers with the same
  ;;; name, but we don't actually care about the scoping details. it helps that in this
  ;;; algorithm (Dunfield-Krishnaswami), ∀'s are never synthesized; they're only destructured

  ; puts a unique #%bvar prop on the identifier so that it can be kept
  ; track of (bvar=?) even after being eval'd
  (define (make-bvar id)
    (mk-type (syntax-property id '#%bvar (gensym (syntax-e #'id)))))

  ; returns #t if x and y are both identifiers that have the same #%bvar prop
  (define (bvar=? x y)
    (and (identifier? x) (identifier? y)
         (eq? (syntax-property x '#%bvar)
              (syntax-property y '#%bvar))))

  ; pattern expander that only matches identifiers that have the same
  ; #%bvar property as the given expression
  (define-syntax ~bvar=
    (pattern-expander
     (syntax-parser
       [(_ bv-expr)
        #:with Y (generate-temporary #'Y)
        #'(~and (~var Y identifier)
                (~fail #:unless (bvar=? bv-expr #'Y)))])))



  ; generates a unique new exis var
  (define (make-exis [pre 'exis])
    (with-syntax ([qs (mk-type #`(quote #,(gensym pre)))])
      ((current-type-eval) #'(Exis qs))))

  ; pattern expander that only matches exis vars that are the same as
  ; the given expression
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
       #:with bX (make-bvar #'X)
       #:with B (ctx-subst (subst #'bX #'X #'A) ctx)
       ; TODO: is there a proper way to transfer syntax properties?
       ; maybe a (type-map f τ) function would be helpful
       ((current-type-eval) (syntax/loc t
                              (∀ (bX) B)))]

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
      [X:id (ormap (lambda (y) (bvar=? #'X y)) ctx)]

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
      ; rigid variables
      [(X:id Y:id) (bvar=? #'X #'Y)]
      [((~and (~Exis _) α1) (~Exis= #'α1)) #t]

      ; hacky way to match two base types
      [(((~literal #%plain-app) A:id) ((~literal #%plain-app) B:id))
       #:when (free-identifier=? #'A #'B)
       #t]
      ; known subtype relations
      ; TODO: don't hardcode this here
      [(~or (~Nat  ~Int)
            (~Int  ~Num)
            (~Nat  ~Num))
       #t]

      [((~→ A1 A2) (~→ B1 B2))
       (and (subtype #'B1 #'A1)
            (subtype (ctx-subst #'A2)
                     (ctx-subst #'B2)))]

      [(A (~∀ (X) B))
       #:with bX (make-bvar #'X)
       #:with B- (subst #'bX #'X #'B)
       (context-push! #'X)
       (begin0 (subtype #'A #'B-)
         (context-pop-until! (~bvar= #'bX)))]

      [((~∀ (X) A) B)
       #:with α (make-exis)
       #:with A- (subst #'α #'X #'A)
       (context-push! #'(Marker α) #'α)
       (begin0 (subtype #'A- #'B)
         (context-pop-until! (~Marker (~Exis= #'α))))]

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
       #:with bX (make-bvar #'X)
       #:with A- (subst #'bX #'X #'A)
       (context-push! #'bX)
       (inst-subtype #'α '<: #'A-)
       (context-pop-until! (~bvar= #'bX))]

      [(~∀ (X) A) #:when (eq? dir ':>)
       #:with β (make-exis)
       #:with A- (subst #'β #'X #'A)
       (context-push! #'(Marker β) #'β)
       (inst-subtype #'α ':> #'A-)
       (context-pop-until! (~Marker (~Exis= #'β)))]

      [_ (raise-inst-subtype-error var t #:src src)]))

  ; exception to be raised by instantiation failure
  (struct exn:fail:inst-subtype exn:fail:syntax (var rhs))
  (define (raise-inst-subtype-error var rhs #:src src)
    (raise (exn:fail:inst-subtype "cannot instantiate"
                                  (current-continuation-marks)
                                  (list src)
                                  var rhs)))
  )
