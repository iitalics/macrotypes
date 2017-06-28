#lang turnstile/lang
(extends "stlc.rkt")

(define-base-types Any Unit Int String Bool)

(provide (type-out Any Int String Bool)
         (typed-out [+ : (→ Int Int Int)]
                    [displayln : (→ Any Unit)]
                    [read : (→ Any)])
         #%datum let cond if error
         integer? string? boolean?)


(define-typed-syntax #%datum
  [(_ . n:exact-integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . s:str) ≫
   --------
   [⊢ (#%datum- . s) ⇒ String]]
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])


(begin-for-syntax
  (define-syntax ~free-id=
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ e)
          (with-syntax ([x (generate-temporary)])
            #'(~and x (~fail #:unless (free-identifier=? #'x e))))]))))

  [current-typecheck-relation
   (λ (t1 t2)
     (or (Any? t2)
         (type=? t1 t2)))]

  [current-var-assign
   (λ (x seps tys)
     (with-syntax ([x x] [(τ) tys])
       #'(#%occvar x : τ)))]
  )

(define-typed-syntax #%occvar
  #:datum-literals (:)
  [(_ x : _) ≫
   #:peek {#:*occ* (~free-id= #'x) : τ_deduced}
   --------
   [⊢ x ⇒ τ_deduced]]

  [(_ x : τ) ≫
   --------
   [⊢ x ⇒ τ]])



(define-syntax define-typed-predicate
  (syntax-parser
    #:datum-literals (⇒)
    [(_ predfn ⇒ type)
     #:with predfn- (format-id #'predfn "~a-" #'predfn)
     #'(define-typed-syntax predfn
         [(_ x:id) ≫
          #:peek* (#:*cond*)
          [⊢ x ≫ x-]
          #:push {#:*occ* x- : type}
          --------
          [⊢ (#%app- predfn- x-) ⇒ Bool]]
         [(_ e:expr) ≫
          [⊢ e ≫ e-]
          --------
          [⊢ (#%app- predfn- e-) ⇒ Bool]])]))

(define-typed-predicate integer? ⇒ Int)
(define-typed-predicate string?  ⇒ String)
(define-typed-predicate boolean? ⇒ Bool)



(define-typed-syntax if
  [(_ p e1 e2) ≫
   #:push #:*cond*
   [⊢ p ≫ p- ⇐ Bool]
   [⊢ e1 ≫ e1- ⇒ τ]
   #:pop* (#:*cond* _ ...)
   [⊢ e2 ≫ e2- ⇐ τ]
   --------
   [⊢ (if- p- e1- e2-) ⇒ τ]])


(define-typed-syntax cond
  #:datum-literals (else)
  [(_ [else e]) ≫
   --------
   [≻ e]]
  [(_ [p0 e0] [p e] ...) ≫
   --------
   [≻ (if p0 e0 (cond [p e] ...))]])


(define-typed-syntax let
  [(_ ([x v] ...) e) ≫
   [⊢ v ≫ v- ⇒ τ] ...
   [[x ≫ x- : τ] ... ⊢ e ≫ e- ⇒ τ_out]
   --------
   [⊢ (let- ([x- v-] ...) e-) ⇒ τ_out]])



(define-typed-syntax error
  [(_ s) ⇐ _ ≫
   [⊢ s ≫ s- ⇐ String]
   --------
   [⊢ (#%app- error- s-) ⇒ Any]]
  [(_ s) ≫
   [⊢ s ≫ s- ⇐ String]
   --------
   [⊢ (#%app- error- s-) ⇒ Any]])
