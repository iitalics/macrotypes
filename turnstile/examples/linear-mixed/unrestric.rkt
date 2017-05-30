#lang turnstile
;; this is a simply typed lambda calculus with tuple
;; destructuring that is slightly generic, so that we
;; can integrate it with the linear part ("linear.rkt")
;; see: ~fun / ~tuple

(define-base-types Unit Int Bool Str)
(define-type-constructor -> #:arity >= 1)
(define-type-constructor × #:arity > 1)

(provide (type-out Unit Int Bool Str -> ×)
         #%datum
         begin let let* if #%app lambda tup
         #%module-begin
         (rename-out [top-interaction #%top-interaction]
                     [lambda λ]))




(begin-for-syntax

  (provide current-parse-fun
           current-parse-tuple
           ~fun
           ~tuple)


  ;; TODO: move these parameters to a seperate common module

  (define current-parse-fun
    (make-parameter
     (syntax-parser
       [(~-> τ ...) #'(τ ...)]
       [_ #f])))

  (define current-parse-tuple
    (make-parameter
     (syntax-parser
       [(~× τ ...) #'(τ ...)]
       [_ #f])))

  (define-syntax ~fun
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ p ...)
          (with-syntax ([tmp (generate-temporary)])
            #'(~and tmp (parse (p ...) ((current-parse-fun) #'tmp))))]))))

  (define-syntax ~tuple
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ p ...)
          (with-syntax ([tmp (generate-temporary)])
            #'(~and tmp (parse (p ...) ((current-parse-tuple) #'tmp))))]))))


  )





; typed syntax

(define-typed-syntax (top-interaction . e) ≫
  [⊢ e ≫ e- ⇒ τ]
  --------
  [≻ (#%app- printf- "~s : ~a\n"
             e-
             '#,(type->str #'τ))])


(define-typed-syntax #%datum
  [(_ . k:exact-integer) ≫
   --------
   [⊢ 'k ⇒ Int]]
  [(_ . k:boolean) ≫
   --------
   [⊢ 'k ⇒ Bool]]
  [(_ . k:str) ≫
   --------
   [⊢ 'k ⇒ Str]])


(define-typed-syntax tup
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (#%app- list- e- ...) ⇒ (× τ ...)]])


(define-typed-syntax begin
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ τ] ...
   #:with τ_out (last (syntax-e #'(τ ...)))
   --------
   [⊢ (begin- e- ...) ⇒ τ_out]])


(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   [⊢ rhs ≫ rhs- ⇒ τ] ...
   [[x ≫ x- : τ] ... ⊢ e ≫ e- ⇒ τ_out]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ τ_out]])


(define-typed-syntax let*
  [(_ ([(x:id ...) rhs] . vars) e) ≫
   [⊢ rhs ≫ rhs- ⇒ (~and τ_tup
                         (~or (~parse (τ ...) ((current-parse-tuple) #'τ_tup))
                              (~post (~fail (format "expected tuple, cannot destructure type ~a"
                                                    (type->str #'τ_tup))))))]

   #:fail-unless (stx-length=? #'(τ ...) #'(x ...)) "wrong number of elements in tuple"
   [[x ≫ x- : τ] ... ⊢ (let* vars e) ≫ e- ⇒ τ_out]

   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (delist (x- ...) rhs- e-) ⇒ τ_out]]

  [(_ ([x:id rhs] . vars) e) ≫
   --------
   [≻ (let ([x rhs]) (let* vars e))]]
  [(_ () e) ≫
   --------
   [≻ e]])

; private macro for destructuring a list into variables
(define-syntax delist
  (syntax-parser
    [(_ () l e) #'e]
    [(_ (x0:id x ...) l e)
     #:with tmp (generate-temporary)
     #'(let*- ([tmp l] [x0 (#%app- car- tmp)]) (delist (x ...) (#%app- cdr- tmp) e))]))



(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- ⇐ Bool]
   [⊢ e2 ≫ e2- ⇒ τ1]
   [⊢ e3 ≫ e3- ⇒ τ2]
   [τ2 τ= τ1 #:for e2]
   --------
   [⊢ (if- e1- e2- e3-) ⇒ τ1]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) ⇒ Unit]]

  [(_ fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ (~and τ_fun
                         (~or (~parse (τ_in ... τ_out) ((current-parse-fun) #'τ_fun))
                              (~post (~fail (format "cannot apply non-function type ~a"
                                                    (type->str #'τ_fun))))))]

   #:fail-unless (stx-length=? #'(τ_in ...) #'(arg ...))
   (format "wrong number of arguments to function, expected ~a, got ~a"
           (stx-length #'(τ_in ...))
           (stx-length #'(arg ...)))

   [⊢ arg ≫ arg- ⇒ τ_arg] ...
   [τ_in τ= τ_arg #:for arg] ...
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ τ_out]])


(define-typed-syntax lambda
  [(_ ([x:id (~datum :) ty:type] ...) body) ≫
   #:with (τ_in ...) #'(ty.norm ...)
   [[x ≫ x- : τ_in] ... ⊢ body ≫ body- ⇒ τ_out]
   --------
   [⊢ (λ- (x- ...) body-) ⇒ (-> τ_in ... τ_out)]])
