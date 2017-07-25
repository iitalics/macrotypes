#lang turnstile
(extends "../ext-stlc.rkt"
         #:except define if begin let let* letrec λ #%app)


(provide (for-syntax current-linear?
                     linear-type?
                     unrestricted-type?
                     linear-scope
                     copy-linear-scope
                     linear-var-in-scope?
                     use-linear-var!
                     pop-linear-context!
                     merge-linear-scopes!)
         (type-out Unit Int String Bool -o)
         #%top-interaction #%module-begin require only-in
         define #%linear
         begin drop let letrec λ #%app if
         (rename-out [λ lambda]))


(define-type-constructor -o #:arity >= 1)


(begin-for-syntax
  (require syntax/id-set)
  (define (sym-diff s0 . ss)
    (for*/fold ([s0 s0])
               ([s (in-list ss)]
                [x (in-set s)])
      (if (set-member? s0 x)
          (set-remove s0 x)
          (set-add s0 x))))


  (define (fail/multiple-use x)
    (raise-syntax-error #f "linear variable used more than once" x))
  (define (fail/unused x)
    (raise-syntax-error #f "linear variable unused" x))
  (define (fail/unbalanced-branches x)
    (raise-syntax-error #f "linear variable may be unused in certain branches" x))
  (define (fail/unrestricted-fn x)
    (raise-syntax-error #f "linear variable may not be used by unrestricted function" x))


  ; current-linear : (Parameter (TypeStx -> Bool))
  (define current-linear?
    (make-parameter (or/c -o?)))

  ; linear-type? : TypeStx -> Bool
  (define (linear-type? t)
    ((current-linear?) t))

  ; unrestricted-type? : TypeStx -> Bool
  (define (unrestricted-type? t)
    (not (linear-type? t)))


  ; linear-scope : FreeIdSet
  ;   holds a list of all linear variables that have been used.
  (define linear-scope
    (make-parameter (mutable-free-id-set)))

  ; linear-var-in-scope? : Id -> Bool
  (define (linear-var-in-scope? x)
    (not (set-member? [linear-scope] x)))

  ; use-linear-var! : Id -> Void
  (define (use-linear-var! x #:fail [fail fail/multiple-use])
    (unless (linear-var-in-scope? x)
      (fail x))
    (set-add! [linear-scope] x))

  ; pop-linear-scope! : StxList -> Void
  ;   drops from scope the linear variables in the given context
  ;   ignores unrestricted types in the context, but checks that
  ;   variables with linear types must be used already.
  ;   the context is a syntax list of the form #'([x τ] ...)
  (define (pop-linear-context! ctx #:fail [fail fail/unused])
    (syntax-parse ctx
      [([X T] ...)
       (define lin-xs
         (immutable-free-id-set
          (for/list ([x (in-syntax #'[X ...])]
                     [t (in-syntax #'[T ...])]
                     #:when (linear-type? t))
            (if (linear-var-in-scope? x)
                (fail x)
                x))))
       (set-subtract! [linear-scope] lin-xs)]))

  ; swap-linear-scope! : FreeIdSet -> FreeIdSet
  ;  swaps the current scope with the given scope, returning the old scope
  (define (copy-linear-scope)
    (mutable-free-id-set
     (set-copy [linear-scope])))

  ; merge-linear-scope! : FreeIdSet -> Void
  ;  ensure that the current scope and the given scope are compatible,
  ;  e.g. when unifying the branches in a conditional
  (define (merge-linear-scopes! mode #:fail [fail fail/unbalanced-branches] . ss)
    (set-clear! [linear-scope])
    (case mode
      [(∩)
       (let* ([s0 (set-copy (car ss))])
         (apply set-intersect! (cons s0 (cdr ss)))
         (for* ([s (in-list ss)]
                [x (in-set s)]
                #:when (not (set-member? s0 x)))
           (fail x))
         (set-clear! [linear-scope])
         (set-union! [linear-scope] s0))]

      [(∪)
       (apply set-union! (cons [linear-scope] ss))]))

  )


(define-typed-variable-syntax
  #:name #%linear
  #:datum-literals [:]
  [(_ x- : σ) ≫ ; record use when σ restricted
   #:do [(unless (unrestricted-type? #'σ)
           (use-linear-var! #'x-))]
   --------
   [⊢ x- ⇒ σ]])


(define-typed-syntax begin
  [(begin e ... e0) ≫
   [⊢ e ≫ e- ⇐ Unit] ...
   [⊢ e0 ≫ e0- ⇒ σ]
   --------
   [⊢ (begin- e- ... e0-) ⇒ σ]])


(define-typed-syntax drop
  [(drop e) ≫
   [⊢ e ≫ e- ⇒ _]
   --------
   [⊢ (#%app- void- e-) ⇒ Unit]])


(define-typed-syntax let
  [(let ([x e_rhs] ...) e ...+) ≫
   [⊢ e_rhs ≫ e_rhs- ⇒ σ] ...
   [[x ≫ x- : σ] ... ⊢ (begin e ...) ≫ e- ⇒ σ_out]
   #:do [(pop-linear-context! #'([x- σ] ...))]
   --------
   [⊢ (let- ([x- e_rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax letrec
  [(letrec ([b:type-bind e_rhs] ...) e) ≫
   #:fail-when (ormap linear-type? (stx->list #'[b.type ...]))
               (format "may not bind linear type ~a in letrec"
                       (type->str (findf linear-type? (stx->list #'[b.type ...]))))
   [[b.x ≫ x- : b.type] ...
    ⊢ [e_rhs ≫ e_rhs- ⇐ b.type] ...
    [e ≫ e- ⇒ σ_out]]
   --------
   [⊢ (letrec- ([x- e_rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax λ
  #:datum-literals (: !)
  ; linear function
  [(λ ([x:id : T:type] ...) e) ≫
   #:with (σ ...) #'(T.norm ...)
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-linear-context! #'([x- σ] ...))]
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (-o σ ... σ_out)]]

  ; unrestricted function
  [(λ ! ([x:id : T:type] ...) e) ≫
   #:with (σ ...) #'(T.norm ...)
   #:do [(define fn-scope (copy-linear-scope))]
   #:mode linear-scope fn-scope
     ([[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
      #:do [(pop-linear-context! #'([x- σ] ...))])
   #:do [(merge-linear-scopes! '∩ [linear-scope] fn-scope #:fail fail/unrestricted-fn)]
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (→ σ ... σ_out)]]

  ; inferred linear function
  [(λ (x:id ...) e) ⇐ (~-o σ ... σ_out) ≫
   #:fail-unless (stx-length=? #'[x ...] #'[σ ...])
   (num-args-fail-msg this-syntax #'[x ...] #'[σ ...])
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇐ σ_out]
   #:do [(pop-linear-context! #'([x- σ] ...))]
   --------
   [⊢ (λ- (x- ...) e-)]]

  ; inferred unrestricted function
  [(λ (x:id ...) e) ⇐ (~→ σ ... σ_out) ≫
   #:fail-unless (stx-length=? #'[x ...] #'[σ ...])
   (num-args-fail-msg this-syntax #'[x ...] #'[σ ...])
   #:do [(define fn-scope (copy-linear-scope))]
   #:mode linear-scope fn-scope
     ([[x ≫ x- : σ] ... ⊢ e ≫ e- ⇐ σ_out]
      #:do [(pop-linear-context! #'([x- σ] ...))])
   #:do [(merge-linear-scopes! '∩ [linear-scope] fn-scope #:fail fail/unrestricted-fn)]
   --------
   [⊢ (λ- (x- ...) e-)]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) ⇒ Unit]]

  [(#%app fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ σ_fun]
   #:with (~or (~-o σ_in ... σ_out)
               (~→ σ_in ... σ_out)
               (~post (~fail "expected linear function type")))
   #'σ_fun
   [⊢ [arg ≫ arg- ⇐ σ_in] ...]
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])


(define-typed-syntax if
  [(if c e1 e2) ≫
   [⊢ c ≫ c- ⇐ Bool]
   #:do [(define scope/then (copy-linear-scope))
         (define scope/else (copy-linear-scope))]
   [⊢ [e1 ≫ e1- ⇒ σ] #:mode linear-scope scope/then]
   [⊢ [e2 ≫ e2- ⇐ σ] #:mode linear-scope scope/else]

   ; (merge branches)
   #:do [(merge-linear-scopes! '∩ scope/then scope/else
                              #:fail fail/unbalanced-branches)]
   --------
   [⊢ (if- c- e1- e2-) ⇒ σ]])


(define-typed-syntax define
  #:datum-literals (:)
  [(define (f [x:id : ty] ...) ret
     e ...+) ≫
   --------
   [≻ (define f : (→ ty ... ret)
        (letrec ([{f : (→ ty ... ret)}
                  (λ ! ([x : ty] ...)
                    (begin e ...))])
          f))]]

  [(_ x:id : τ:type e:expr) ≫
   #:fail-when (linear-type? #'τ.norm)
               "cannot define linear type globally"
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e : τ.norm)))]])
