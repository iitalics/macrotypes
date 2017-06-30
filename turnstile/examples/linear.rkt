#lang turnstile

(provide (type-out Unit Int Str Bool -o ⊗ !!)
         #%top-interaction #%module-begin require only-in
         #%datum begin tup let λ #%app if
         (rename-out [λ lambda]))

(provide (typed-out [+ : (!! (-o Int Int Int))]
                    [< : (!! (-o Int Int Bool))]
                    [displayln : (!! (-o Str Unit))]))

(define-base-types Unit Int Str Bool)
(define-type-constructor -o #:arity >= 1)
(define-type-constructor ⊗ #:arity = 2)
(define-type-constructor !! #:arity = 1)

(begin-for-syntax
  (define-syntax ~free-id=
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ e)
          (with-syntax ([x (generate-temporary)])
            #'(~and (~var x identifier)
                    (~fail #:unless (free-identifier=? #'x e))))]))))

  (define unrestricted-type?
    (or/c Bool? Unit? Int? !!?))


  (define (fail/multiple-use x)
    (raise-syntax-error #f "linear variable used more than once" x))

  (define (fail/unused x)
    (raise-syntax-error #f "linear variable unused" x))

  (define (fail/unused/branch x)
    (raise-syntax-error #f "linear variable may be unused in certain branches" x))

  (define (fail/unrestriced-scope x)
    (raise-syntax-error #f "linear variable may not be used by unrestricted function" x))

  )


(define-typed-syntax #%top-interaction
  [(_ . e) ≫
   [⊢ e ≫ e- ⇒ τ]
   --------
   [≻ (#%app- printf- '"~a : ~a\n"
              e-
              '#,(type->str #'τ))]])


(define-typed-syntax #%datum
  [(_ . n:exact-integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (#%datum- . s) ⇒ Str]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])


(begin-for-syntax
  [current-var-assign
   (lambda (x seps types)
     #`(#%linvar #,x : #,(stx-car types)))])

(define-typed-syntax #%linvar
  #:datum-literals (:)
  [(_ x : σ) ≫
   #:when (unrestricted-type? #'σ)
   --------
   [⊢ x ⇒ σ]]

  [(_ x : _) ≫
   #:peek (~free-id= #'x)
   #:do [(fail/multiple-use #'x)]
   --------
   [#:error -]]

  [(_ x : σ) ≫
   #:push x
   --------
   [⊢ x ⇒ σ]])


(define-typed-syntax begin
  [(_ e ... e0) ≫
   [⊢ [e ≫ e- ⇒ _] ... [e0 ≫ e0- ⇒ σ]]
   --------
   [⊢ (begin- e- ... e0-) ⇒ σ]])


(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (⊗ σ1 σ2)]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) ⇒ Unit]]

  [(#%app fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ σ_fun]
   #:with (~or (~-o σ_in ... σ_out)
               (~!! (~-o σ_in ... σ_out))
               (~post (~fail "expected function type")))
          #'σ_fun
   [⊢ [arg ≫ arg- ⇐ σ_in] ...]
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])



(define-for-syntax (linear-xs x/ts)
  (for/list ([pair (in-syntax x/ts)]
             #:when (not (unrestricted-type? (stx-cdr pair))))
    (stx-car pair)))

(define-for-syntax (out-of-scope xs scope)
  (for/fold ([scope scope])
            ([x (in-syntax xs)])
    (syntax-parse scope
      [(lo ... (~free-id= x) hi ...) #'(lo ... hi ...)]
      [_ (fail/unused x)])))

(define-for-syntax (merge-scopes scope1 scope2 #:fail fail)
  (syntax-parse (list scope1 scope2)
    [[() ()] #'()]
    [[(x . xs) ys]
     #:with (lo ... (~free-id= #'x) hi ...) #'ys
     #:with scope- (merge-scopes #'xs #'(lo ... hi ...) #:fail fail)
     #'(x . scope-)]
    [(~or [(x . xs) _]
          [_ (x . xs)])
     (fail #'x)]))


(define-typed-syntax let
  #:datum-literals (∇)
  [(let ([x e] ...) e_body) ≫
   [⊢ [e ≫ e- ⇒ σ] ...]
   #:push ∇
   [[x ≫ x- : σ] ... ⊢ e_body ≫ e_body- ⇒ σ_body]
   #:pop* (∇ tos ...)
   #:with (tos- ...) (out-of-scope (linear-xs #'([x- . σ] ...)) #'(tos ...))
   #:push* (tos- ...)
   --------
   [⊢ (let- ([x- e-] ...) e_body-) ⇒ σ_body]])


(define-typed-syntax if
  #:datum-literals (∇)
  [(if e0 e1 e2) ≫
   [⊢ e0 ≫ e0- ⇐ Bool]
   #:push ∇ [⊢ e1 ≫ e1- ⇒ σ] #:pop* (∇ tos1 ...)
   #:push ∇ [⊢ e2 ≫ e2- ⇐ σ] #:pop* (∇ tos2 ...)
   #:with (tos- ...) (merge-scopes #'(tos1 ...) #'(tos2 ...) #:fail fail/unused/branch)
   #:push* (tos- ...)
   --------
   [⊢ (if- e0- e1- e2-) ⇒ σ]])


(define-typed-syntax λ
  #:datum-literals (∇ !)
  [(_ ([x : T:type] ...) e) ≫
   #:with (σ ...) #'[T.norm ...]
   #:push ∇
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:pop* (∇ tos ...)
   #:with (tos- ...) (out-of-scope (linear-xs #'([x- . σ] ...)) #'(tos ...))
   #:push* (tos- ...)
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (-o σ ... σ_out)]]

  [(_ ! ([x : T:type] ...) e) ≫
   #:with (σ ...) #'[T.norm ...]
   #:push ∇
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:pop* (∇ tos ...)
   #:with (tos- ...) (out-of-scope (linear-xs #'([x- . σ] ...)) #'(tos ...))
   #:with _ (merge-scopes #'(tos- ...) #'() #:fail fail/unrestriced-scope)
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (!! (-o σ ... σ_out))]])
