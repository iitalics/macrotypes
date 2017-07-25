#lang turnstile/lang
(extends "lin.rkt")
(require (only-in "lin+tup.rkt" gen-cad*rs))

(provide ⊕ var match)

(define-internal-type-constructor ⊕/i)

(define-syntax ⊕
  (syntax-parser
    [(_ (V:id t ...) ...)
     (add-orig (mk-type #'(⊕/i- (#%app 'V t ...) ...))
               this-syntax)]))

(begin-for-syntax
  (provide ⊕? ~⊕)
  (define ⊕? ⊕/i?)

  (define (unvariant type)
    (syntax-parse type
      [(~⊕/i ((~literal #%plain-app) ((~literal quote) U) τ ...) ...)
       #'[(U τ ...) ...]]))

  (define-syntax ~⊕
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ . pat)
          (with-syntax ([(x) (generate-temporaries #'(x))])
            #'(~and x (~⊕/i . _) (~parse pat (unvariant #'x))))]))))

  (define (has-variant? type v)
    (syntax-parse type
      [(~⊕ [U . _] ...)
       (for/or ([u (in-syntax #'[U ...])])
         (eq? (stx->datum u) (stx->datum v)))]
      [_ #f]))

  (define (variant-names type)
    (syntax-parse type
      [(~⊕ [U . _] ...) (stx->datum #'[U ...])]
      [_ '()]))

  (define (get-variant type v)
    (syntax-parse type
      [(~⊕ [U τ ...] ...)
       (for/first ([u (in-syntax #'[U ...])]
                   [ts (in-syntax #'[(τ ...) ...])]
                   #:when (eq? (stx->datum u) (stx->datum v)))
         ts)]))

  (define (fail/no-variant type V [src V])
    (raise-syntax-error #f
       (format "expected type ~a does not have variant named '~a'\n"
               (type->str type)
               (stx->datum V))
       src))

  [current-linear? (or/c ⊕? [current-linear?])]
  )


(define-typed-syntax var
  [(_ [V:id e ...]) ⇐ σ_var ≫
   #:when (⊕? #'σ_var)
   #:fail-unless (has-variant? #'σ_var #'V)
                 (fail/no-variant #'σ_var #'V this-syntax)
   #:with [σ ...] (get-variant #'σ_var #'V)
   #:fail-unless (stx-length=? #'[σ ...] #'[e ...])
                 (format "expected ~a arguments to variant, got ~a"
                         (stx-length #'[σ ...])
                         (stx-length #'[e ...]))
   [⊢ e ≫ e- ⇐ σ] ...
   --------
   [⊢ (list 'V e- ...)]]

  [(_ [V:id e ...] (~datum as) t) ≫
   --------
   [≻ (lin:ann (var [V e ...]) : t)]])



(define-typed-syntax match
  [(_ e_var [(V:id x:id ...) e_bra] ...) ≫
   [⊢ e_var ≫ e_var- ⇒ σ_var]
   #:fail-unless (⊕? #'σ_var)
   (format "expected type ⊕, given ~a" (type->str #'σ_var))

   #:do [(define scope/branches
           (stx-map (λ (_) (copy-linear-scope)) #'[e_bra ...]))]

   #:with ([(x- ...) e_bra- σ_bra] ...)
   (for/list ([S (in-list scope/branches)]
              [q (in-syntax #'([V (x ...) e_bra] ...))])
     (syntax-parse/typecheck q
       [(V (x ...) e) ≫
        #:fail-unless (has-variant? #'σ_var #'V)
                      (fail/no-variant #'σ_var #'V)
        #:with [σ ...] (get-variant #'σ_var #'V)
        #:fail-unless (stx-length=? #'[σ ...] #'[x ...])
        (format "trying to match ~a arguments to variant '~a', expected ~a"
                (stx-length #'[x ...])
                (syntax-e #'V)
                (stx-length #'[σ ...]))

        #:mode linear-scope S
          ([[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_bra]
           #:do [(pop-linear-context! #'([x- σ] ...))])
        --------
        [≻ [(x- ...) e- σ_bra]]]))

   #:do [(apply merge-linear-scopes! (cons '∩ scope/branches))]

   #:with tmp (generate-temporary)
   #:with ((cad*r/tmp ...) ...)
   (stx-map (λ (xs)
              (map (gen-cad*rs #'(cdr tmp))
                   (range (stx-length xs))))
            #'((x ...) ...))
   --------
   [⊢ (let ([tmp e_var-])
        (case (car tmp)
          [(V) (let ([x- cad*r/tmp] ...)
                 e_bra-)] ...
          [else (printf "~a\n" tmp)
                (error '"unhandled case: " (car tmp))]))
      ⇒ (⊔ σ_bra ...)]])
