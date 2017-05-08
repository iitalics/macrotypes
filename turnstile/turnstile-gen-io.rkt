#lang racket





(module phase1-params racket/base
  (provide (all-defined-out))

  ; default keys when using `⇒ templ' syntax
  ; instead of specifying with `(⇒ key templ)'
  (define default-input-key
    (make-parameter 'expected-type))
  (define default-output-key
    (make-parameter ':))

  (define expected-outputs-key
    (make-parameter '#%expected-outputs))
  )


(module syntax-classes racket/base
  (require syntax/parse
           racket/syntax
           (only-in racket/set subset?)
           (for-meta -1 (only-in macrotypes/typecheck infer))
           (submod ".." phase1-params))
  (provide (all-defined-out))


  (define (get-props stx keys)
    (let/ec break
      (for/list ([key (in-list keys)])
        (or (syntax-property stx key)
            (break #f)))))

  (define (put-props stx keys vals)
    (foldl (lambda (k v out)
             (syntax-property out k v))
           stx keys vals))

  (define (transfer-props-list dst src keys)
    (foldl (lambda (k out)
             (syntax-property out k (syntax-property src k)))
           dst keys))




  ; TODO: non-unicode alternatives (#:keywords?)
  (define-syntax-class d⇐
    (pattern (~datum ⇐)))
  (define-syntax-class d⇒
    (pattern (~datum ⇒)))
  (define-syntax-class d≫
    (pattern (~datum ≫)))
  (define-syntax-class d⊢
    (pattern (~datum ⊢)))
  (define-syntax-class d≻
    (pattern (~datum ≻)))

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




  (define-splicing-syntax-class tag⇐
    (pattern (:d⇐ key expr))
    (pattern (~seq :d⇐ expr)
             #:with key (default-input-key)))

  (define-splicing-syntax-class tag⇒
    (pattern (:d⇒ key expr))
    (pattern (~seq :d⇒ expr)
             #:with key (default-output-key)))


  (define-splicing-syntax-class ellipses
    (pattern (~seq (~literal ...))
             #:with repeat? #t)
    (pattern (~seq)
             #:with repeat? #f))



  (define current-rule-input-keys
    (make-parameter '()))

  (define-syntax-class tych-rule
    (pattern [expr-patn in:tag⇐ ... ~! :d≫
                        premise:tych-premise ...
                        :----
                        concl:tych-conclusion]
             #:with norm
             #'[expr-patn
                #:with (in.expr ...) (get-props this-syntax
                                                '(in.key ...))
                concl.pre ...
                premise.norm ... ...
                concl.post ...
                (parameterize ([current-rule-input-keys '(in.key ...)])
                  concl.result)]))



  (define-splicing-syntax-class tych-premise
    ; syntax-parse directive premise
    (pattern dir:stxparse-dir
             #:with [norm ...] #'dir)

    ; premise with expression and tags
    (pattern (~seq [:d⊢ template :d≫ pattern
                        in:tag⇐ ...
                        out:tag⇒ ...] ooo:ellipses)
             #:with e* (generate-temporary #'prem+tags)
             #:with e+ (generate-temporary #'prem-infer)
             #:with [norm ...]
             #`[#:with e*
                (put-props (syntax-property #`template
                                            '#,(expected-outputs-key)
                                            '(out.key ...))
                           '(in.key ...)
                           (list #`in.expr ...))
                #:with (_ _ (e+) _) (infer (list #'e*))
                #:with pattern #'e+
                #:with (out.expr ...) (get-props #'e+ '(out.key ...))]))



  (define-syntax-class tych-conclusion
    ; conclusion extends
    (pattern [:d≻ template]
             #:with [pre ...] #'[]
             #:with [post ...] #'[]
             #:with keys-expr #`(cons '#,(expected-outputs-key)
                                      (current-rule-input-keys))
             #:with result
             #'(transfer-props-list #`template
                                    this-syntax
                                    keys-expr))

    ; conclusion outputs
    (pattern [:d⊢ template
                  out:tag⇒ ...]
             #:with [pre ...]
             #`[#:when (subset? (or (syntax-property this-syntax '#,(expected-outputs-key))
                                    '())
                                '(out.key ...))]
             #:with [post ...] #'[]
             #:with result #'(put-props #`template
                                        '(out.key ...)
                                        (list #`out.expr ...)))

    ; conclusion errors
    (pattern [#:error err-msg]
             #:with [pre ...] #'[]
             #:with [post ...] #'[];#'[#:fail-unless #f err-msg]
             #:with result
             #'(raise-syntax-error #f err-msg this-syntax)))

  (define-syntax-class (tych-parser-body fallback?)
    (pattern [options:stxparse-options
              rule:tych-rule ...]
             #:with [opts ...] #'options
             #:with [maybe-fallback ...] (if fallback?
                                             #'[[_ (parse/fallback this-syntax)]]
                                             #'[])
             #:with [norm ...]
             #'[opts ...
                rule.norm ...
                maybe-fallback ...]))


  (define fallback-parsers '())

  (define (parse/fallback stx)
    (or (for/or ([parser (in-list fallback-parsers)])
          (parser stx))
        (raise-syntax-error #f "no matching clauses" stx)))

  (define (add-fallback! name fn)
    (set! fallback-parsers
          (append fallback-parsers
                  (list fn))))

  )

(require (for-meta 1
                   'syntax-classes
                   syntax/parse
                   racket/syntax))

(define-syntax define-typed-syntax
  (syntax-parser
    [(_ name:id . (~var body (tych-parser-body #t)))
     #'(define-syntax name
         (syntax-parser
           body.norm ...))]

    [(_ (name:id . pats) :d≫ . r)
     #'(define-typed-syntax name
         [(_ . pats) ≫ . r])]))

(define-syntax define-typed-fallbacks
  (syntax-parser
    [(_ name:id . (~var body (tych-parser-body #f)))
     #'(begin-for-syntax
         (add-fallback! 'name
                        (syntax-parser
                          body.norm ...
                          [_ #f])))]))



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



(define-typed-fallbacks chk->inf
  [e
   (⇐ expected-type τ_in) ≫
   [⊢ e ≫ e- ⇒ τ_out]
   #:do [(printf "reverted to inference.\n")]
   #:when ((current-typecheck-relation) #'τ_out #'τ_in)
   --------
   [⊢ e-]]

  [_ ≫
   --------
   [#:error "no expected type; add annotations"]])

(define-typed-syntax t/dat
  [(_ . k:integer) ≫
   -------
   [⊢ 'k ⇒ Int]])

(define-typed-syntax t/lam
  #:datum-literals (->)
  [(_ (x) e) ⇐ (-> A B) ≫
   [⊢ e ≫ e- ⇐ B]
   --------
   [⊢ (lambda (x) e-)]])

(define-typed-syntax t/ann
  [(_ e (~datum :) τ) ≫
   [⊢ e ≫ e- ⇐ τ]
   --------
   [⊢ e- ⇒ τ]])

(define-typed-syntax (typeof e) ≫
  [⊢ e ≫ e- ⇒ τ]
  --------
  [≻ 'τ])

(displayln (typeof (t/dat . 4)))
(displayln         (t/dat . 4))
(displayln (t/ann (t/dat . 4) : Float))



#|

SYNTAX:
(syntax-parse/typecheck
  <stx-expr>
  <sp-option> ...
  <tych-rule> ...)

<sp-option>
  = <`syntax-parse` option>

<tych-rule>
  = [<expr-pattern>
     (⇐ <key-id> <pattern>) ...
     ≫
     <tych-premise> ...
     --------
     <tych-conclusion>]

<tych-premise>
  = <`syntax-parse` pattern directive>
  | [<ctx-elem> ...
     ⊢
     <expr-templ> ≫ <expr-pattern>
     (⇐ <key-id> <template>) ...
     (⇒ <key-id> <pattern>) ...] ooo

<ctx-elem>
  = [<var-id> ≫ <var-pattern>
     <key-id> <type-template> ... ...] ooo

<tych-conclusion>
  = [⊢ <expr-template> (⇒ <key-id> <template>) ...]
  | [≻ <expr-template>]
  | [#:error <expression>]



|#
