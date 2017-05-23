#lang turnstile
(require (for-syntax racket/set
                     syntax/id-set))

; type system
(define-base-types Int Bool Unit)
(define-type-constructor × #:arity = 2)   ; pair
(define-type-constructor -> #:arity >= 1) ; unrestricted function
(define-type-constructor -o #:arity >= 1) ; linear function
(define-type-constructor Box #:arity = 1) ; mutable box

(define-base-type Δ)

(provide (type-out Int Bool Unit Box × -> -o)
         box tup
         #%datum #%app let let-values if lambda
         (rename-out [#%module-begin #%module-begin]
                     [top-interaction #%top-interaction]
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
  ; (linear? type) -> boolean
  (define linear?
    (syntax-parser
      [(~Box _) #t]
      [(~-o _ ...) #t]
      [(~× a b) (or (linear? #'a) (linear? #'b))]
      [_ #f]))



  ;; create a linear term with the given information
  (define (make-lin-term used-vars
                         ; ref-vars
                         )
    (put-props #'Δ
               '#%term-used-vars used-vars))


  ;; extract information from linear terms
  (define (lin-used-vars a) (syntax-property a '#%term-used-vars))


  ;; expand a linear term
  (define (expand-lin-term a)
    ((current-type-eval) a))




  ;; make a linear term for a variable with the given type
  (define (make-linear-var orig type)
    (cond
      [(linear? type)
       (let ([tmp (put-props (generate-temporary)
                             'orig orig)])
         (make-lin-term (immutable-free-id-set (list tmp))))]
      [else
       (make-empty-lin-term)]))

  ;; make an linear term that does nothing
  (define (make-empty-lin-term)
    (make-lin-term (immutable-free-id-set)))



  ;; symmetric difference implementation, because current impl for
  ;; id-tables is bugged
  (define (sym-dif s1 s2)
    (for/fold ([s s1])
              ([x (in-set s2)])
      (if (free-id-set-member? s x)
          (free-id-set-remove s x)
          (free-id-set-add s x))))

  )




;; linear combinators

(define-syntax LNop
  ; linear logic:  1 & A
  (syntax-parser
    [(_) (make-empty-lin-term)]

    [(_ #:src src A)
     #:with A- (expand-lin-term #'A)
     (for ([v (in-set (lin-used-vars #'A-))])
       (raise-syntax-error #f "linear variable not allowed in this context"
                           #'src
                           (syntax-property v 'orig)))
     (make-empty-lin-term)]))

(define-syntax LSeq
  ; linear logic:  A ⅋ ...
  (syntax-parser
    [(_ A ...)
     (let ([used-vars
            (for/fold ([used (immutable-free-id-set)])
                      ([term (in-list (syntax-e #'(A ...)))])
              (let ([term-used (lin-used-vars (expand-lin-term term))])
                (for ([v (in-set (set-intersect used term-used))])
                  (raise-syntax-error #f "linear variable used more than once"
                                      (syntax-property v 'orig)))
                (set-union used term-used)))])
       (make-lin-term used-vars))]))

(define-syntax LIntro
  ; linear logic:  (A ⊗ ...) -o B
  (syntax-parser
    [(_ #:src src A ... B)
     (let ([new-vars (for/fold ([vars (immutable-free-id-set)])
                               ([term (in-list (syntax-e #'(A ...)))])
                       (set-union vars (lin-used-vars (expand-lin-term term))))]
           [used-vars (lin-used-vars (expand-lin-term #'B))])
       (for ([v (in-set (set-subtract new-vars used-vars))])
        (raise-syntax-error #f "linear variable unused"
                             #'src
                             (syntax-property v 'orig)))
       (make-lin-term (set-subtract used-vars new-vars)))]))

(define-syntax LJoin
  ; linear logic:  A & B
  (syntax-parser
    [(_ #:src src A B)
     (let ([used-a (lin-used-vars (expand-lin-term #'A))]
           [used-b (lin-used-vars (expand-lin-term #'B))])
       (for ([v (in-set (sym-dif used-a used-b))])
         (raise-syntax-error #f "linear variable may be unused"
                             #'src
                             (syntax-property v 'orig)))
       (make-lin-term used-a))]))






(define-typed-syntax #%datum
  [(_ . k:integer) ≫
   --------
   [⊢ 'k (⇒ : Int) (⇒ % (LNop))]]
  [(_ . k:boolean) ≫
   --------
   [⊢ 'k (⇒ : Bool) (⇒ % (LNop))]])


(define-typed-syntax box
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   --------
   [⊢ (#%app- box- e-)
      (⇒ : (Box τ))
      (⇒ % A)]])


(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- (⇒ : τ1) (⇒ % A)]
   [⊢ e2 ≫ e2- (⇒ : τ2) (⇒ % B)]
   --------
   [⊢ (#%app- list- e1- e2-)
      (⇒ : (× τ1 τ2))
      (⇒ % (LSeq A B))]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void) (⇒ : Unit) (⇒ % (LNop))]]

  [(_ fun arg ...) ≫
   [⊢ fun ≫ fun-
            (⇒ : (~or (~-> τ_in ... τ_out)
                      (~-o τ_in ... τ_out)
                      (~post (~and τ
                                   (~fail (format "expected -> or -o type, got: ~a"
                                                  (type->str #'τ)))))))
            (⇒ % A)]
   #:fail-unless (stx-length=? #'(τ_in ...)
                               #'(arg ...))
   "wrong number of arguments to function"

   [⊢ arg ≫ arg- (⇒ : τ_arg) (⇒ % B)] ...
   [τ_arg τ= τ_in #:for arg] ...
   --------
   [⊢ (#%app- fun- arg- ...)
      (⇒ : τ_out)
      (⇒ % (LSeq A B ...))]])


(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   #:with here this-syntax
   [⊢ rhs ≫ rhs- (⇒ : τ) (⇒ % A)] ...
   #:with (Lx ...) (map make-linear-var
                        (syntax-e #'(x ...))
                        (syntax-e #'(τ ...)))
   [[x ≫ x- : τ % Lx] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒ % B)]
   --------
   [⊢ (let- ([x- rhs-] ...) e-)
      (⇒ : τ_out)
      (⇒ % (LSeq A ... (LIntro #:src here
                               Lx ... B)))]])


(define-typed-syntax let-values
  [(_ ([(x:id y:id) rhs] ...) e) ≫
   #:with here this-syntax
   [⊢ rhs ≫ rhs- (⇒ : (~× τ1 τ2)) (⇒ % A)] ...
   #:with (Lx ...) (map make-linear-var
                        (syntax-e #'(x ...))
                        (syntax-e #'(τ1 ...)))
   #:with (Ly ...) (map make-linear-var
                        (syntax-e #'(y ...))
                        (syntax-e #'(τ2 ...)))
   [([x ≫ x- : τ1 % Lx] ...)
    ([y ≫ y- : τ2 % Ly] ...)
    ⊢ e ≫ e- (⇒ : τ_out) (⇒ % B)]

   #:with (tmp ...) (generate-temporaries #'(rhs ...))
   --------
   [⊢ (let- ([tmp rhs-] ...)
            (let- ([x- (#%app- car- tmp)] ...
                   [y- (#%app- cadr- tmp)] ...)
                  e-))
      (⇒ : τ_out)
      (⇒ % (LSeq A ... (LIntro #:src here
                               Lx ...
                               Ly ... B)))]])


(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   #:with here this-syntax
   [⊢ e1 ≫ e1- (⇒ : ~Bool) (⇒ % A)]
   [⊢ e2 ≫ e2- (⇒ : τ1) (⇒ % B1)]
   [⊢ e3 ≫ e3- (⇒ : τ2) (⇒ % B2)]
   [τ2 τ= τ1 #:for e3]
   --------
   [⊢ (if- e1- e2- e3-)
      (⇒ : τ1)
      (⇒ % (LSeq A (LJoin #:src here B1 B2)))]])


(define-typed-syntax lambda
  [(_ ([x:id (~datum :) t:type] ...) e) ≫
   #:with here this-syntax
   #:with (τ ...) #'(t.norm ...)
   #:with (Lx ...) (map make-linear-var
                        (syntax-e #'(x ...))
                        (syntax-e #'(τ ...)))
   [[x ≫ x- : τ % Lx] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒ % A)]
   --------
   [⊢ (λ- (x- ...) e-)
      (⇒ : (-> τ ... τ_out))
      (⇒ % (LNop #:src here
                 (LIntro #:src here
                         Lx ... A)))]])






;; redefine #%top-interaction and #%module-begin to check
;; linear terms after typechecking.

(define-typed-syntax (top-interaction . e) ≫
  [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
  --------
  [≻ (#%app- printf '"~s : ~a\n"
             e-
             '#,(type->str #'τ))])





;; testing

(require rackunit
         (for-syntax (only-in racket/string string-contains?)))

(provide check-linear)

(define-typed-syntax check-linear
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ % A)]
   #:do [(expand-lin-term #'(LNop #:src e A))]
   --------
   [≻ (#%app- check-true '#t)]]

  [(_ e #:fail msg) ≫
   --------
   [≻
    #,(with-handlers
        ([(and/c exn:fail:syntax?
                 (lambda (ex)
                   (string-contains? (exn-message ex)
                                     (syntax-e #'msg))))
          (lambda _
            #'(#%app- check-true '#t))])
        (syntax-parse '()
          [((~⊢ e ≫ e- (⇒ : τ) (⇒ % A)))
           (expand-lin-term #'(LNop #:src e A))
           #'(#%app- fail '"expected failure, but expression succeeded.")]))]])
