#lang turnstile
(require (prefix-in SM/ "sm.rkt"))

(provide (rename-out [@%module-begin #%module-begin]
                     [@%datum #%datum]
                     [@%app #%app]
                     [@if if]))

(define-base-type Int)
(define-base-type Bool)
(define-type-constructor -> #:arity > 0)

(provide (typed-out [[SM/+ : (-> Int Int Int)] +]
                    [[SM/- : (-> Int Int Int)] -]
                    [[SM/* : (-> Int Int Int)] *]
                    [[SM// : (-> Int Int Bool)] /]
                    [[SM/< : (-> Int Int Bool)] <]
                    [[SM/> : (-> Int Int Bool)] >]
                    [[SM/= : (-> Int Int Bool)] =]))


(define-syntax @%module-begin
  (syntax-parser
    [(_ toplvl ...)
     ; TODO: parse defines using syntax-local-lift-...
     #'(SM/#%module-begin
        (SM/do toplvl SM/.d) ...)]))

(define-typed-syntax @%datum
  [(_ . n:exact-integer) ≫
   --------
   [⊢ (SM/#%datum . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   --------
   [⊢ (SM/#%datum . b) ⇒ Bool]])

(define-typed-syntax @%app
  [(_ f e ...) ≫
   [⊢ f ≫ f- ⇒ (~-> τ ... τ_out)]
   [⊢ [e ≫ e- ⇐ τ] ...]
   #:do [(printf "expanded:\n")
         (for ([el (in-syntax #'[e- ...])])
           (printf "  ~a\n" (syntax->datum el)))]
   --------
   [⊢ (SM/do e- ... f-) ⇒ τ_out]])

(define-typed-syntax @if
  [(_ c e_1 e_2) ≫
   [⊢ c ≫ c- ⇐ Bool]
   [⊢ e_1 ≫ e_1- ⇒ τ]
   [⊢ e_2 ≫ e_2- ⇐ τ]
   --------
   [⊢ (SM/do c- (SM/if [e_1-] [e_2-])) ⇒ τ]])
