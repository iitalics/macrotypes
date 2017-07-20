#lang turnstile/lang
(extends "lin.rkt")

(provide (all-from-out "lin.rkt")
         (type-out ⊗)
         tup let*)

(define-type-constructor ⊗ #:arity >= 2)

(begin-for-syntax
  (define (num-tuple-fail-msg σs xs)
    (format "wrong number of tuple elements: expected ~a, got ~a"
            (stx-length xs)
            (stx-length σs)))

  [current-linear? (or/c ⊗? [current-linear?])])


(define-typed-syntax tup
  [(_ e1 e2 ...+) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2] ...
   --------
   [⊢ (#%app- list- e1- e2- ...) ⇒ (⊗ σ1 σ2 ...)]])


(define-typed-syntax let*
  [(_ () e) ≫
   --------
   [≻ e]]

  ; normal let* recursive bindings
  [(_ ([x:id e_rhs] . xs) e_body) ≫
   [⊢ e_rhs ≫ e_rhs- ⇒ σ]
   [[x ≫ x- : σ] ⊢ (let* xs e_body) ≫ e_body- ⇒ σ_out]
   #:do [(pop-linear-context! #'([x- σ]))]
   --------
   [⊢ (let- ([x- e_rhs-]) e_body-) ⇒ σ_out]]

  ; tuple unpacking with (let* ([(x ...) tup]) ...)
  [(_ ([(x ...) e_rhs] . xs) e_body) ≫
   [⊢ e_rhs ≫ e_rhs- ⇒ (~⊗ σ ...)]
   #:fail-unless (stx-length=? #'[σ ...] #'[x ...])
                 (num-tuple-fail-msg #'[σ ...] #'[x ...])

   [[x ≫ x- : σ] ... ⊢ (let* xs e_body) ≫ e_body- ⇒ σ_out]
   #:do [(pop-linear-context! #'([x- σ] ...))]

   #:with tmp (generate-temporary #'e_tup)
   #:with (cad*r/tmp ...) (map (gen-cad*rs #'tmp)
                               (range (stx-length #'[x ...])))
   --------
   [⊢ (let*- ([tmp e_rhs-] [x- cad*r/tmp] ...) e_body-) ⇒ σ_out]])

; gen-cad*rs : Id -> Int -> Stx
;  e.g. ((gen-cad*rs #'x) 3) = #'(car (cdr (cdr (cdr x))))
(define-for-syntax ((gen-cad*rs tmp) n)
  #`(#%app- car-
            #,(for/fold ([e tmp])
                        ([i (in-range n)])
                #`(#%app- cdr- #,e))))
