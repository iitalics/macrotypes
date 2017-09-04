#lang turnstile/lang
(require (prefix-in core: "core.rkt")
         (for-syntax turnstile/mode))

(provide define-type
         define-predicate
         define-stage
         define
         interactive
         #%datum * +
         #%app (rename-out [quot quote]))

(define-base-types Term Stage)
(define-type-constructor Pred #:arity >= 0)
(define-type-constructor Rule #:arity = 2)

(define-syntax define-type
  (syntax-parser
    [(_ T:id)
     #:with T- (generate-temporary #'T)
     #'(begin-
         (define-syntax T
           (make-rename-transformer (add-orig (mk-type #'T-) #'T)))
        (define- T- (#%app- core:type)))]))


(define-typed-syntax define
  #:literals (#%type)
  #:datum-literals (:)
  [(_ obj : τ) ≫
   [⊢ τ ≫ τ- (⇒ :: #%type)]
   #:with obj- (generate-temporary #'obj)
   --------
   [≻ (begin-
        (define-syntax obj
          (make-rename-transformer (⊢ obj- : τ)))
        (define- obj-
          (#%app- core:unique 'obj 'obj-)))]])


(define-typed-syntax define-predicate
  #:literals (#%type)
  [(_ (predicate τ:type ...)) ≫
   [⊢ [τ ≫ τ- (⇒ :: #%type)] ...]
   #:with predicate- (generate-temporary #'predicate)
   #:with (arg ...) (generate-temporaries #'(τ ...))
   --------
   [≻ (begin-
        (define-syntax predicate
          (make-rename-transformer (⊢ predicate- : (Pred τ ...))))
        (define- (predicate- arg ...)
          (#%app- core:predicate 'predicate 'predicate-
                  (#%app- list arg ...))))]])


(define-typed-syntax #%datum
  [(_ . 1) ≫
   --------
   [⊢ (#%app- core:one) ⇒ Term]]

  [(_ . 0) ≫
   --------
   [⊢ (#%app- core:zero) ⇒ Term]])


(define-typed-syntax *
  [(_ t ...) ≫
   [⊢ [t ≫ t- ⇐ Term] ...]
   --------
   [⊢ (#%app- core:⊗* t- ...) ⇒ Term]])


(define-typed-syntax +
  [(_ t ...) ≫
   [⊢ [t ≫ t- ⇐ Term] ...]
   --------
   [⊢ (#%app- core:⊕* t- ...) ⇒ Term]])





(define-typed-syntax #%app
  [(_ p arg ...) ≫
   [⊢ p ≫ p- ⇒ (~Pred τ ...)]
   #:fail-unless (stx-length=? #'[τ ...] #'[arg ...])
   (num-args-fail-msg #'p #'[τ ...] #'[arg ...])
   [⊢ [arg ≫ arg- ⇐ τ] ...]
   --------
   [⊢ (#%app- p- arg- ...) ⇒ Term]])


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
          ([⊢ in ≫ in- ⇐ Term]
           [⊢ out ≫ out- ⇐ Term]
           #:with (var-id ...) (hash-keys (rule-var-types-hash)))
        --------
        [≻ ['rule-name (#%app- core:rule '(var-id ...) in- out-)]]]))

   #:with stage- (generate-temporary #'stage)
   --------
   [≻ (begin-
        (define-syntax stage
          (make-rename-transformer (⊢ stage- : Stage)))
        (define- stage-
          (#%app- core:stage
                  'stage
                  (#%app- hash rule-hash-entry- ... ...))))]])


(define-typed-syntax interactive
  [(_ stg { t ... }) ≫
   [⊢ stg ≫ stg- ⇐ Stage]
   [⊢ [t ≫ t- ⇐ Term] ...]
   --------
   [≻ (#%app- core:interactive
              (#%app- core:⊗* t- ...)
              stg-)]]

  [(_ stg) ≫
   --------
   [≻ (interactive stg {})]])
