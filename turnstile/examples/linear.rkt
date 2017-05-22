#lang turnstile

; type system
(define-base-types Int Bool Unit)
(define-type-constructor × #:arity = 2)   ; pair
(define-type-constructor -> #:arity >= 1) ; unrestricted function
(define-type-constructor -o #:arity >= 1) ; linear function
(define-type-constructor Box #:arity = 1) ; mutable box

; linear logic
(define-type-constructor Then #:arity >= 1) ; A ⅋ B ...
(define-type-constructor Both #:arity = 2) ; A & B ...
(define-base-type Nop)
(define-base-type NewVar)
(define-base-type UseVar)

(provide (type-out Int Bool Unit Box × -> -o)
         #%datum box tup
         begin #%app let if cond lambda
         #%top-interaction
         (rename-out [module-begin #%module-begin]
                     [lambda λ])
         require)

(begin-for-syntax

  ; put multiple syntax properties onto the given syntax object
  ; (put-props stx key1 val1 key2 val2 ...) -> stx-
  (define-syntax (put-props stx)
    (syntax-case stx ()
      [(_ expr key val . rst)
       #'(put-props (syntax-property expr key val) . rst)]
      [(_ expr)
       #'expr]))


  ; is the given type a linear type?
  ; (is-linear? type) -> boolean
  (define is-linear?
    (syntax-parser
      [(~Box _) #t]
      [(~-o _ ...) #t]
      [(~× a b) (or (is-linear? #'a) (is-linear? #'b))]
      [_ #f]))


  ; generates a list of two linear terms, first for the creation of
  ; the variable (x↑), and second for the use of the variable (x↓). if given an
  ; unrestricted type, returns (Nop Nop), otherwise returns (NewVar UseVar),
  ; both corresponding to the variable.
  ; (mk-var-dual stx type) -> (list δ-new δ-use)
  (define (mk-var-dual orig type)
    (cond
      [(is-linear? type)
       (let ([uniq-id (gensym)])
         (map (lambda (stx)
                (put-props stx
                           '#%id uniq-id
                           '#%orig orig))
              (list
               ((current-type-eval) (syntax/loc orig NewVar))
               ((current-type-eval) (syntax/loc orig UseVar)))))]
      [else
       (list ((current-type-eval) #'Nop)
             ((current-type-eval) #'Nop))]))


  ; check if the list of linear terms (e.g. Then, All, NewVar, etc.) represent
  ; a consistent program. raises an exception if variables are determined to be
  ; overused to underused.
  ; (linear term-list) -> void
  (define (linear terms [ctx (hash)])

    (define (ctx-check-empty)
      (for ([(id orig) (in-hash ctx)])
        (raise-syntax-error #f
                            "linear variable may be unused"
                            orig)))

    (define (ctx-new-var v)
      (hash-set ctx
                (syntax-property v '#%id)
                (syntax-property v '#%orig)))

    (define (ctx-use-var v)
      (let ([id (syntax-property v '#%id)])
        (unless (hash-has-key? ctx id)
          (raise-syntax-error #f
                              "linear variable may be used more than once"
                              (syntax-property v '#%orig)))
        (hash-remove ctx id)))

    (syntax-parse terms
      [{} (ctx-check-empty)]
      [{(~Both A1 A2) B ...}    (linear #'(A1 B ...) ctx)
                                (linear #'(A2 B ...) ctx)]
      [{(~Then A ...) B ...}    (linear #'(A ... B ...) ctx)]
      [{(~and ~NewVar v) B ...} (linear #'(B ...) (ctx-new-var #'v))]
      [{(~and ~UseVar v) B ...} (linear #'(B ...) (ctx-use-var #'v))]
      [{~Nop B ...}             (linear #'(B ...) ctx)]))

  )



;; datum produces Nop since no linear variables are created or used

(define-typed-syntax #%datum
  [(_ . k:integer) ≫
   --------
   [⊢ 'k (⇒ : Int) (⇒ % Nop)]]
  [(_ . k:boolean) ≫
   --------
   [⊢ 'k (⇒ : Bool) (⇒ % Nop)]])



;; these simply forward / combine the linear terms of their subexpressions

(define-typed-syntax box
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   --------
   [⊢ (#%app- box- e-) (⇒ : (Box τ)) (⇒ % A)]])


(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- (⇒ : τ1) (⇒ % A)]
   [⊢ e2 ≫ e2- (⇒ : τ2) (⇒ % B)]
   --------
   [⊢ (#%app- list- e1- e2-)
      (⇒ : (× τ1 τ2))
      (⇒ % (Then A B))]])


(define-typed-syntax begin
  [(_ e1 ... e2) ≫
   [⊢ e1 ≫ e1- (⇒ : _) (⇒ % A)] ...
   [⊢ e2 ≫ e2- (⇒ : τ) (⇒ % B)]
   --------
   [⊢ (begin- e1- ... e2-)
      (⇒ : τ)
      (⇒ % (Then A ... B))]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) (⇒ : Unit) (⇒ % Nop)]]

  [(_ fun arg ...) ≫
   [⊢ fun ≫ fun-
            ; note that #%app makes no distinction between linear/nonlinear function
            (⇒ : (~or (~-> τ_in ... τ_out)
                      (~-o τ_in ... τ_out)
                      (~post (~and τ
                                   (~fail (format "expected -> or -o type, got: ~a"
                                                  (type->str #'τ)))))))
            (⇒ % A)]
   #:fail-unless (stx-length=? #'{τ_in ...}
                               #'{arg ...})
   "wrong number of arguments to function"

   [⊢ arg ≫ arg- (⇒ : τ_arg) (⇒ % B)] ...
   [τ_arg τ= τ_in #:for arg] ...
   --------
   [⊢ (#%app- fun- arg- ...)
      (⇒ : τ_out)
      (⇒ % (Then A B ...))]])


;; to introduce new variables, we call mk-var-dual, have
;; the variables expand to x↓ when they are used, and then introduce
;; x↑ ourselves in the output

(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- (⇒ : τ) (⇒ % A)] ...
   #:with ((x↑ x↓) ...) (map mk-var-dual
                             (syntax-e #'(x ...))
                             (syntax-e #'(τ ...)))
   [[x ≫ x- : τ % x↓] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒ % B)]
   --------
   [⊢ (let- ([x- rhs-] ...) e-)
      (⇒ : τ_out)
      (⇒ % (Then A ... x↑ ... B))]])



;; combine the linear terms of the branching parts of (if ...) using
;; (Both ...) instead of (Then ...)

(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- (⇒ : ~Bool) (⇒ % A)]
   [⊢ e2 ≫ e2- (⇒ : τ1) (⇒ % B)]
   [⊢ e3 ≫ e3- (⇒ : τ2) (⇒ % C)]
   #:fail-unless (type=? #'τ1 #'τ2)
   (format "conflicting types in branches: ~a and ~a"
           (type->str #'τ1)
           (type->str #'τ2))
   --------
   [⊢ (if- e1- e2- e3-)
      (⇒ : τ1)
      (⇒ % (Then A (Both B C)))]])


(define-syntax cond
  (syntax-parser
    [(_ [(~datum else) expr ...])    #'(begin expr ...)]
    [(_ [test expr ...] others ...+) #'(if test
                                           (begin expr ...)
                                           (cond others ...))]))



;; the linear function is the same as (let ...), but the unrestricted
;; function makes use of (Both ...) in a non-obvious way, by combining
;; it with Nop. this works because an unrestricted function doesn't need to be
;; called, so we account for that case as if its a branch. this also solves
;; the problem of unrestricted functions being called multiple times, since
;; we are forced (by the Nop branch) to use the linear variables later on in
;; the code, which would cause a double-use error.

(define-typed-syntax lambda
  #:datum-literals (: once)
  ; linear function
  [(_ once ({x:id : t:type} ...) e) ≫
   #:with (τ_in ...) #'(t.norm ...)
   #:with ((x↑ x↓) ...) (map mk-var-dual
                             (syntax-e #'(x ...))
                             (syntax-e #'(τ_in ...)))
   [[x ≫ x- : τ_in % x↓] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒ % B)]
   --------
   [⊢ (λ- (x- ...) e-)
      (⇒ : (-o τ_in ... τ_out))
      (⇒ % (Then x↑ ... B))]]

  ; unrestricted function
  [(_ ({x:id : t:type} ...) e) ≫
   #:with (τ_in ...) #'(t.norm ...)
   #:with ((x↑ x↓) ...) (map mk-var-dual
                             (syntax-e #'(x ...))
                             (syntax-e #'(τ_in ...)))
   [[x ≫ x- : τ_in % x↓] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒ % B)]
   --------
   [⊢ (λ- (x- ...) e-)
      (⇒ : (-> τ_in ... τ_out))
      (⇒ % (Both Nop (Then x↑ ... B)))]])



;; redefine #%top-interaction and #%module-begin to check
;; linear terms after typechecking.

(define-syntax module-begin
  (syntax-parser
    [(_ e ...)
     #:with (e- ...)
     (map (syntax-parser
            [((~or (~literal require)
                   (~literal define)). _)
             this-syntax]
            [e #'(check-me e)])
          (syntax-e #'(e ...)))
     #'(#%module-begin
        e- ...)]))

(define-syntax check-me
  (syntax-parser
    [(~and (_ e)
           [~⊢ e ≫ e- (⇒ : τ) (⇒ % A)])
     (begin
       (when (syntax-e #'A)
         (linear #'{A}))
       #'e-)]))

(define-typed-syntax (#%top-interaction . e) ≫
  [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
  #:do [(linear #'{A})]
  --------
  [≻ (#%app- printf '"~s : ~a\n"
             e-
             '#,(type->str #'τ))])



;; define our own typed-out for linear types
;; this is mainly copied from macrotypes.rkt

(require (for-syntax syntax/transformer))

; i wrote this because make-variable-like-transformer was insufficient
(define-for-syntax (type+lin-transformer ref-stx ty lin)
  (make-set!-transformer
   (syntax-parser
     [:id (put-props ref-stx
                     ': (syntax-local-introduce ((current-type-eval) ty))
                     '% (syntax-local-introduce ((current-type-eval) lin)))]
     [(x . tail)
      #:with ap (datum->syntax this-syntax '#%app)
      #`(ap x . tail)])))


(define-syntax lin-typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       #:datum-literals (:)
       [(_ [x:id : ty:type (~parse out-x #'x)] ...)
        #:with (x/tc ...) (generate-temporaries #'(x ...))
        #:when (stx-map
                syntax-local-lift-module-end-declaration
                #'{(define-syntax x/tc
                     (type+lin-transformer #'x #'ty #'Nop)) ...})
        (pre-expand-export (syntax/loc stx (rename-out [x/tc out-x] ...))
                           modes)]))))


;; standard library

(provide (lin-typed-out [+ : (-> Int Int Int)]
                        [< : (-> Int Int Bool)]
                        [inc : (-> (Box Int) (Box Int))]
                        [take-int : (-> (Box Int) Int)]))

(define- (inc b)
  (#%app- set-box!- b (#%app- add1- (#%app- unbox- b)))
  b)

(define- (take-int b)
  (#%app- unbox- b))




;; test functions (TODO: put in another file)

(provide check-type
         check-linear)

(require (for-syntax (prefix-in RU: rackunit))
         (only-in racket/string string-contains?)
         (only-in racket/function negate)
         (prefix-in RU: rackunit))

(define-typed-syntax check-type
  #:datum-literals (: =)

  [(_ e : t:type) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   #:do [(RU:check type=? #'t.norm #'τ
                   (format "Type check failure ~a vs ~a"
                           (type->str #'t.norm)
                           (type->str #'τ)))
         (linear #'{A})]
   --------
   [⊢ (#%app- RU:check-true '#t) (⇒ : Unit) (⇒ % Nop)]]

  [(_ e #:fail) ≫
   #:with r (with-handlers ([exn:fail? (lambda _
                                         (syntax/loc #'e (#%app- RU:check-true '#t)))])
              (syntax-parse '()
                [([~⊢ e ≫ e- (⇒ : τ) (⇒ % A)])
                 (syntax/loc #'e (#%app- RU:fail '"Expected type check failure"))]))
   --------
   [⊢ r (⇒ : Unit) (⇒ % Nop)]])


(define-typed-syntax check-linear
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   #:do [(linear #'{A})]
   --------
   [⊢ (#%app- RU:check-true '#t) (⇒ : Unit) (⇒ % Nop)]]

  [(_ e #:fail) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   #:with r (with-handlers ([exn:fail:syntax? (lambda _ (syntax/loc #'e
                                                     (#%app- RU:check-true '#t)))])
              (linear #'{A})
              (syntax/loc #'e
                (#%app- RU:fail '"expected linearity failure")))
   --------
   [⊢ r (⇒ : Unit) (⇒ % Nop)]]

  [(_ e #:fail msg) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   #:with r (with-handlers ([exn:fail:syntax? (lambda (ex)
                                                (quasisyntax/loc #'e
                                                  (#%app- RU:check
                                                          string-contains?
                                                          '#,(exn-message ex)
                                                          'msg
                                                          '"expected failure message to match")))])
              (linear #'{A})
              (syntax/loc #'e
                (#%app- RU:fail '"expected linearity failure")))
   --------
   [⊢ r (⇒ : Unit) (⇒ % Nop)]])
