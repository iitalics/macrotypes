#lang racket


(module phase1-params racket/base
  (provide (all-defined-out))

  ; default tags when using `⇒ templ' syntax
  ; instead of specifying with `(⇒ tag expr)'
  (define default-input-tag
    (make-parameter 'expected-type))
  (define default-output-tag
    (make-parameter ':))


  ; tags containing lists of the input tags and
  ; the expected output tags for typechecking
  ; e.g. for
  ;  [⊢ e ≫ e- (⇐ X x) (⇐ Y y) (⇒ Z z)]
  ; we would set the following syntax properties on 'e':
  ;   'X  = #`x
  ;   'Y  = #`y
  ;   '#%turnstile-inputs  = '(X Y)
  ;   '#%turnstile-outputs = '(Z)
  (define input-list-property
    (make-parameter '#%turnstile-inputs))
  (define output-lists-property
    (make-parameter '#%turnstile-outputs))
  )


(module syntax-classes racket/base
  (require syntax/parse
           racket/syntax
           (submod ".." phase1-params)
           (only-in racket/set set=? subset?)
           (for-syntax racket/base syntax/parse racket/syntax))

  (provide typechecking
           tags⇐ tags⇒
           rule
           premise
           clause
           #;conclusion)


  (define-syntax-class ----
    #:commit
    (pattern dashes:id
             #:fail-unless (regexp-match? #px"-{4,}"
                                          (symbol->string (syntax-e #'dashes)))
             "expected a line of three or more -'s (e.g. -----)"))



  (define-splicing-syntax-class stxparse-options
    (pattern (~seq (~seq (~or #:context
                              #:literals
                              #:datum-literals
                              #:literal-sets
                              #:conventions
                              #:local-conventions) ~!
                              argument)
                   ...)))

  (define-splicing-syntax-class stxparse-dir
    (pattern (~or (~seq (~or #:and #:post #:when #:do) ~!
                        argument)
                  (~seq (~or #:fail-when #:fail-unless
                             #:with #:attr) ~!
                             argument expression))))



  (define-splicing-syntax-class tags⇐
    #:datum-literals (⇐ ⇒ ≫)
    #:attributes ([tags 1] [exprs 1])
    (pattern (~seq ⇐ tag:id (~and expr (~not (~or ≫ ⇐ ⇒))))
             #:with [tags ...] #'[tag]
             #:with [exprs ...] #'[expr])
    (pattern (~seq ⇐ expr)
             #:with [tags ...] #`[#,(default-input-tag)]
             #:with [exprs ...] #'[expr])
    (pattern (~seq (⇐ tags:id exprs) ...)))

  (define-splicing-syntax-class tags⇒
    #:datum-literals (⇐ ⇒ ≫)
    #:attributes ([tags 1] [exprs 1])
    (pattern (~seq ⇒ tag:id (~and expr (~not (~or ≫ ⇐ ⇒))))
             #:with [tags ...] #'[tag]
             #:with [exprs ...] #'[expr])
    (pattern (~seq ⇒ expr)
             #:with [tags ...] #`[#,(default-output-tag)]
             #:with [exprs ...] #'[expr])
    (pattern (~seq (⇒ tags:id exprs) ...)))

  (define-syntax-class ellipsis
    (pattern (~literal ...)))
  (define-splicing-syntax-class ellipsi
    (pattern (~seq (~literal ...) ...)))



  (define (get-prop stx key [def #f])
    (or (syntax-property stx key) def))

  (define (get-props stx keys)
    (map (lambda (k) (get-prop stx k)) keys))

  (define (put-props stx keys vals)
    (foldl (lambda (k v s) (syntax-property s k v))
           stx keys vals))




  (define-syntax-class rule
    #:datum-literals (≫)
    (pattern [pattern in:tags⇐ ~! ≫
                      premise:premise/directive ...
                      :----
                      conclusion]
             #:with get-input-list #`(get-prop this-syntax '#,(input-list-property) '())
             #:with norm #'[pattern
                            #:when (set=? '(in.tags ...) get-input-list)
                            #:with (in.exprs ...) (get-props this-syntax '(in.tags ...))
                            premise.norm ... ...
                            conclusion]))

  (define-splicing-syntax-class premise/directive
    (pattern spdir:stxparse-dir
             #:with [norm ...] #'spdir)
    (pattern prem:premise
             #:with [norm ...] #'[prem.norm ...]))



  (define-splicing-syntax-class premise
    #:datum-literals (⊢)
    (pattern (~seq [e:ctx-elem ~! ⊢ c:clause ...] ooos:ellipsi)
             #:with [norm ...] #'[]))

  (define-splicing-syntax-class ctx-elem
    #:datum-literals (≫)
    (pattern (~seq [var:id ~! ≫ pattern
                           (~seq tags:id tag-templs) ...]
                   ooos:ellipsi)))

  (define-splicing-syntax-class clause
    #:datum-literals (≫)
    (pattern (~seq [template ~! ≫ pattern
                             in:tags⇐
                             out:tags⇒]
                   ooos:ellipsi)))



  (define-syntax-class typechecking
    (pattern [options:stxparse-options
              rule:rule ...]
             #:with [opts ...] #'options
             #:with [norm ...] #'[opts ... rule.norm ...]))

  )

(require (for-meta 1 'syntax-classes)
         (for-meta 2 'syntax-classes)
         (for-syntax racket/base syntax/parse racket/syntax))



(begin-for-syntax
  (define (simple-type=? t1 t2)
    (syntax-parse (list t1 t2)
      [((e1 ...) (e2 ...))
       #:when (= (length (syntax-e #'(e1 ...)))
                 (length (syntax-e #'(e2 ...))))
       (andmap simple-type=?
               (syntax-e #'(e1 ...))
               (syntax-e #'(e2 ...)))]
      [(x:id y:id) (free-identifier=? #'x #'y)]
      [_ #f]))

  (define current-typecheck-relation
    (make-parameter simple-type=?)))


(define-syntax define-typed-syntax
  (syntax-parser
    [(_ name:id . body:typechecking)
     #'(define-syntax (name the-stx)
         (syntax-parse the-stx
           body.norm ...))]

    [(_ (name:id . pats) . r)
     #'(define-typed-syntax name
         [(_ . pats) . r])]))



(define-typed-syntax (vars [x e1 e2] ...) ≫
  [[x ≫ x- : Int]
   ⊢
   [e1 ≫ e1- ⇐ Int]
   [e2 ≫ e2- ⇐ Int]]
  --------
  #''ok)
