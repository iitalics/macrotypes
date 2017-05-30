#lang turnstile
;; this is a mix of the linear and unrestricted languages, with
;; explicit language barrier to go from unrestric->linear

(require (prefix-in U: "unrestric.rkt")
         (prefix-in L: "linear.rkt")
         (only-in "unrestric.rkt"
                  Unit Int Bool Str -> × ~-> ~×
                  current-parse-fun
                  current-parse-tuple
                  ~fun
                  ~tuple)
         (only-in "linear.rkt"
                  Box -o ⊗ ~-o ~⊗
                  linear-type?
                  ))

(provide (rename-out [U:#%top-interaction #%top-interaction]
                     [U:#%datum #%datum]
                     [U:begin begin]
                     [U:#%app #%app])
         #%module-begin
         let let* lambda
         tup box unbox
         l)

(begin-for-syntax

  (define linear-lang?
    (make-parameter #f))

  ; accept either function type
  [current-parse-fun
   (syntax-parser
     [(~-> σ ...) #'(σ ...)]
     [(~-o σ ...) #'(σ ...)]
     [_ #f])]

  ; accept either tuple type
  [current-parse-tuple
   (syntax-parser
     [(~× σ ...) #'(σ ...)]
     [(~⊗ σ ...) #'(σ ...)]
     [_ #f])]

  )

#|
          Unrestr     Linear    Lin-only    New
#%datum      ×
begin        ×
let          ×    !!    ×
let*         ×    !!    ×
if           ×    !!    ×
#%app        ×
lambda       ×    !!    ×
tup          ×    !!    ×
box                                ×
unbox                              ×
l                                            ×
share                                        ×

|#

(define-typed-syntax let
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:let . args)]]

  [(_ . args) ≫
   #:when (not [linear-lang?])
   --------
   [≻ (U:let . args)]])


(define-typed-syntax let*
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:let* . args)]]

  [(_ . args) ≫
   --------
   [≻ (U:let* . args)]])


(define-typed-syntax if
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:if . args)]]

  [(_ . args) ≫
   --------
   [≻ (U:if . args)]])


(define-typed-syntax lambda
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:lambda . args)]]

  [(_ . args) ≫
   --------
   [≻ (U:lambda . args)]])


(define-typed-syntax tup
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:tup . args)]]

  [(_ . args) ≫
   --------
   [≻ (U:tup . args)]])


(define-typed-syntax box
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:box . args)]]

  [(_ . args) ≫
   --------
   [#:error "cannot use linear-only syntax here"]])


(define-typed-syntax unbox
  [(_ . args) ≫
   #:when [linear-lang?]
   --------
   [≻ (L:unbox . args)]]

  [(_ . args) ≫
   --------
   [#:error "cannot use linear-only syntax here"]])


(define-typed-syntax l
  [(_ e) ≫
   #:when (not [linear-lang?])
   #:with (_ _ (e-) (τ))
   (parameterize ([linear-lang? #t])
     (infer (list #'e)))

   #:do [(when (linear-type? #'τ)
           (raise-syntax-error #f
                               (format "linear type ~a cannot escape linear context"
                                       (type->str #'τ))
                               #'e))]
   --------
   [⊢ e- ⇒ τ]]

  [(_ _) ≫
   --------
   [#:error "redundant use of syntax; already in linear context"]])
