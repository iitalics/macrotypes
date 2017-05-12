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
; marking
(define-type-constructor Marking #:arity = 1)


(provide (type-out Unit Nat Int Num Exis → ∀))

(begin-for-syntax
  (require racket/base
           syntax/parse
           (for-syntax syntax/parse))

  (provide make-exis ~Exis= Exis=?
           subtype
           well-formed?)


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
        #:with tmp (generate-temporary)
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


  ; implements the subtyping algorithm [Γ ⊢ A <: B ⊣ Δ] using
  ; global state to handle contexts. returns #t if t1 can be make a subtype of t2
  (define (subtype t1 t2)
    (syntax-parse (list t1 t2)
      [(A B)
       #:when (type=? #'A #'B)
       #t]

      [(~or (~Nat  ~Int)
            (~Int  ~Num)
            (~Nat  ~Num))
       #t]

      [((~and (~Exis _) α1) (~Exis= #'α1))
       #t]

      [((~→ A1 A2) (~→ B1 B2))
       (and (subtype #'B1 #'A1)
            (subtype #'A2 #'B2))]

      [_ #f]))


  ; implement the instantiation algorithm [Γ ⊢ α <:= A ⊣ Δ] using
  ; global state to handle contexts. instantiate so that subtyping
  ; is determined by dir, e.g.
  ;   if dir = '<: then α <: t
  ;   if dir = ':> then t <: α
  (define (inst-subtype var dir t #:src [src t])
    (define/with-syntax α var)
    (syntax-parse t
      [τ
       #:when (well-formed? #'τ (context-before (~Exis= #'α)))
       (context-replace! (~Exis= #'α)
                         #'(α . Exis:= . τ))]

      [_
       (raise-syntax-error 'instantiation
                           "cannot instantiate"
                           src)]))


  ; checks if the type is well formed under the context segment
  ; which is the algorithm [Γ ⊢ τ]
  (define (well-formed? t [ctx (the-context)])
    (syntax-parse t
      [X:id (member #'X ctx type=?)]

      [(~→ A B)
       (and (well-formed? #'A ctx)
            (well-formed? #'B ctx))]

      [(~and (~Exis _) α)
       (ormap (syntax-parser
                [(~Exis= #'α) #t]
                [(~Exis:= (~Exis= #'α) _) #t]
                [_ #f])
              ctx)]

      [(~∀ (X) A)
       (well-formed? #'A (cons #'X ctx))]

      [_ #t]))


  )
