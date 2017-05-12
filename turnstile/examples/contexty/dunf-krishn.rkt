#lang turnstile/lang
(require "context.rkt")

(define-base-type Unit)
(define-base-type Nat)
(define-base-type Int)
(define-base-type Num)

(define-type-constructor → #:arity = 2)
(define-binding-type ∀ #:bvs = 1 #:arity = 1)

(define-type-constructor Exis #:arity = 1)

(provide (type-out Unit Nat Int Num Exis → ∀))

(begin-for-syntax
  (require racket/base
           syntax/parse
           (for-syntax syntax/parse))

  (provide make-exis ~Exis= Exis=?
           subtype)


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

  )
