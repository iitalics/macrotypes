#lang turnstile/lang
(require (prefix-in core: "core.rkt")
         (for-syntax turnstile/mode)
         (only-in macrotypes/stx-utils
                  make-variable-like-transformer))

(provide define
         #%datum * +
         (rename-out [app #%app] [quot quote])
         define-stage
         interactive
         Type Pred)


(define-base-types Stage)
(define-type-constructor → #:arity >= 1)
(define-type-constructor Rule #:arity = 2)

(define Type- (core:object 'Type '#%type '()))
(define-syntax Type
  (syntax-parser
    [:id
     (add-orig
      (mk-type
       (attach #'Type- ': #'Type))
      this-syntax)]))

(begin-for-syntax
  (current-typecheck-relation
   (let ([tck (current-typecheck-relation)])
     (λ (t1 t2)
       (or (and (type=? t1 #'Type)
                (type=? t2 #'Type-))
           (tck t1 t2))))))

(define-typed-syntax define
  #:literals (#%type)
  #:datum-literals (:)
  [(_ obj:id : τ) ≫
   [⊢ τ ≫ τ- ⇐ Type]
   #:with obj- (generate-temporary #'obj)
   --------
   [≻ (begin (define-syntax obj
               (syntax-parser
                 [(~var _ id)
                  (add-orig (mk-type (⊢ obj- : τ))
                            #'obj)]))
              (define- obj-
                (core:object 'obj 'obj- '())))]]

  [(_ (obj:id τ ...+) : σ) ≫
   [⊢ [τ ≫ τ- ⇐ Type] ... [σ ≫ σ- ⇐ Type]]
   #:with obj- (generate-temporary #'obj)
   #:with (arg ...) (generate-temporaries #'[τ ...])
   --------
   [≻ (begin (define-syntax obj
               (make-rename-transformer
                (⊢ obj- : (→ τ ... σ))))
             (define- obj-
               (procedure-rename
                (λ (arg ...)
                  (core:object 'obj 'obj- (#%app- list arg ...)))
                'obj)))]])


(define Pred : Type)

(define-typed-syntax #%datum
  [(_ . 1) ≫
   --------
   [⊢ (core:one) ⇒ Pred]]

  [(_ . 0) ≫
   --------
   [⊢ (core:zero) ⇒ Pred]])


(define-typed-syntax *
  [(_ t ...) ≫
   [⊢ [t ≫ t- ⇐ Pred] ...]
   --------
   [⊢ (core:⊗* t- ...) ⇒ Pred]])


(define-typed-syntax +
  [(_ t ...) ≫
   [⊢ [t ≫ t- ⇐ Pred] ...]
   --------
   [⊢ (core:⊕* t- ...) ⇒ Pred]])



(define-typed-syntax app
  [(_ p arg ...) ≫
   [⊢ p ≫ p- ⇒ (~→ τ ... σ)]
   #:fail-unless (stx-length=? #'[τ ...] #'[arg ...])
                 (num-args-fail-msg #'p #'[τ ...] #'[arg ...])
   [⊢ [arg ≫ arg- ⇐ τ] ...]
   --------
   [⊢ #,(mk-type #'(#%app- p- arg- ...)) ⇒ σ]])


(begin-for-syntax
  (struct rule-def mode (vars))

  (define (make-rule-def)
    (rule-def void void (make-hash)))

  (define (rule-var-types-hash)
    (rule-def-vars (current-mode)))

  (define (get-var-type id)
    (hash-ref (rule-var-types-hash)
              (syntax-e id)
              #f))

  (define (set-var-type id T)
    (hash-set! (rule-var-types-hash)
               (syntax-e id)
               T)))

(define-typed-syntax quot
  [_ ≫
   #:when (not (rule-def? (current-mode)))
   --------
   [#:error "invalid use of quote outside of rule definition"]]

  [(_ x:id) ≫
   #:when (get-var-type #'x)
   --------
   [⊢ 'x ⇒ #,(get-var-type #'x)]]

  [(_ x:id) ⇐ τ ≫
   #:do [(set-var-type #'x #'τ)]
   --------
   [⊢ 'x]])




(define-typed-syntax define-stage
  #:datum-literals (-o)
  [(_ stage (rule-name in -o out) ...) ≫

   #:with ([rule-hash-entry- ...] ...)
   (for/list ([stx (in-syntax #'([rule-name in out] ...))])
     (syntax-parse/typecheck stx
       [(rule-name in out) ≫
        #:mode (make-rule-def)
          ([⊢ in ≫ in- ⇐ Pred]
           [⊢ out ≫ out- ⇐ Pred]
           #:with (var-id ...) (hash-keys (rule-var-types-hash)))
        --------
        [≻ ['rule-name (core:rule '(var-id ...) in- out-)]]]))

   #:with stage- (generate-temporary #'stage)
   --------
   [≻ (begin-
        (define-syntax stage
          (make-rename-transformer (⊢ stage- : Stage)))
        (define- stage-
          (core:stage 'stage
                      (hash rule-hash-entry- ... ...))))]])


(define-typed-syntax interactive
  [(_ stg { t ... }) ≫
   [⊢ stg ≫ stg- ⇐ Stage]
   [⊢ [t ≫ t- ⇐ Pred] ...]
   --------
   [≻ (core:interactive (core:⊗* t- ...) stg-)]]

  [(_ stg) ≫
   --------
   [≻ (interactive stg {})]])
