#lang turnstile
;; this is a mix of the linear and unrestricted languages, with
;; explicit language barrier to go from unrestric->linear

(require (prefix-in U: "unrestric.rkt")
         (prefix-in L: "linear.rkt")

         (only-in "unrestric.rkt"
                  Unit Int Bool Str -> × ~-> ~×
                  ;
                  unrestric-parse-fun
                  unrestric-parse-tuple
                  current-parse-fun
                  current-parse-tuple
                  ~fun
                  ~tuple)

         (only-in "linear.rkt"
                  -o ⊗ ~-o ~⊗ Box Loc !! ~!!
                  ;
                  linear-parse-fun
                  linear-parse-tuple
                  linear-type?
                  infer/lin-vars
                  infer/branch
                  ))

(provide Unit Int Bool Str -> × -o ⊗ Box Loc !!
         (rename-out [U:#%top-interaction #%top-interaction]
                     [U:#%datum #%datum]
                     [U:begin begin]
                     [U:#%app #%app]
                     [L:if if])
         #%module-begin
         let let* lambda tup
         box unbox share
         l)


#|
Syntax    Unrestr     Linear    New
#%datum      ×
begin        ×
let          ×          ×
let*         ×          ×
if           ×          ×
#%app        ×
lambda       ×          ×
tup          ×          ×
box                     ×
unbox                   ×
share                   ×        ×
l                                ×

|#



(begin-for-syntax

  (define linear-lang?
    (make-parameter #f))

  ; parse types from either language
  [current-parse-fun
   (λ (ty) (or (unrestric-parse-fun ty)
               (linear-parse-fun ty)))]
  [current-parse-tuple
   (λ (ty) (or (unrestric-parse-tuple ty)
               (linear-parse-tuple ty)))]

  ; convert linear type to unrestricted type, or return #f if
  ; not possible
  (define (linear->unrestricted ty)
    (let/ec ec
      ((current-type-eval)
       (let l->u ([ty ty])
         (syntax-parse ty

           [(~⊗ σ ...)
            #:with (τ ...) (stx-map l->u #'(σ ...))
            (syntax/loc ty (× τ ...))]
           [(~-o σ ...)
            #:with (τ ...) (stx-map l->u #'(σ ...))
            (syntax/loc ty (-> σ ...))]
           [(~!! σ)
            #:with τ (l->u #'σ)
            (syntax/loc ty τ)]

           [_ (if (linear-type? ty)
                  (ec #f)
                  ty)])))))

  )


(define-syntax redefine-syntax
  (syntax-parser
    [(_ x:id (~and kw
                   (~or #:linear
                        #:unrestric
                        #:both)))
     #:with tmp (generate-temporary)
     #:with x/L (format-id #'x "L:~a" #'x)
     #:with x/U (format-id #'x "U:~a" #'x)
     #`(define-typed-syntax x
         [(_ . tmp) ≫
          #:when [linear-lang?]
          --------
          #,(case (syntax-e #'kw)
              [(#:unrestric) #'[#:error "cannot use unrestricted syntax in linear context"]]
              [else #'[≻ (x/L . tmp)]])]
         [(_ . tmp) ≫
          #:when (not [linear-lang?])
          --------
          #,(case (syntax-e #'kw)
              [(#:linear) #'[#:error "cannot use linear syntax in unrestricted context"]]
              [else #'[≻ (x/U . tmp)]])])]))


(redefine-syntax let   #:both)
(redefine-syntax let*  #:both)
(redefine-syntax lambda #:both)
(redefine-syntax tup   #:both)
(redefine-syntax box   #:linear)
(redefine-syntax unbox #:linear)
(redefine-syntax share #:linear)


(define-typed-syntax l
  [(_ e) ≫
   #:when (not [linear-lang?])
   #:with (_ _ (e-) (σ))
   (parameterize ([linear-lang? #t])
     (infer (list #'e)))

   #:with τ (linear->unrestricted #'σ)
   #:do [(unless (syntax-e #'τ)
           (raise-syntax-error #f
                               (format "linear type ~a cannot escape linear context"
                                       (type->str #'σ))
                               this-syntax))]
   --------
   [⊢ e- ⇒ τ]]

  [(_ _) ≫
   --------
   [#:error "redundant use of syntax; already in linear context"]])
