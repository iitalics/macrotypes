#lang racket
(require macrotypes/typecheck
         syntax/parse
         (for-syntax racket/base
                     syntax/parse)
         (for-template syntax/parse))

(provide syntax-parse/typecheck)

(begin-for-syntax

  ; TODO: non-unicode alternatives (#:keywords?)
  (define-syntax-class ⇐
    (pattern (~datum ⇐)))
  (define-syntax-class ⇒
    (pattern (~datum ⇒)))
  (define-syntax-class ≫
    (pattern (~datum ≫)))
  (define-syntax-class ⊢
    (pattern (~datum ⊢)))
  (define-syntax-class ≻
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




  (define default-input-key
    (make-parameter 'expected-type))

  (define default-output-key
    (make-parameter ':))

  ; #f to not require rules to match expected outputs
  (define expected-output-list-key
    (make-parameter '#%expected-outputs))

  (define-splicing-syntax-class tag⇐
    (pattern (:⇐ key expr))
    (pattern (~seq :⇐ expr)
             #:with key (default-input-key)))

  (define-splicing-syntax-class tag⇒
    (pattern (:⇒ key expr))
    (pattern (~seq :⇒ expr)
             #:with key (default-output-key)))

  (define-splicing-syntax-class ellipses
    (pattern (~seq (~literal ...)))
    (pattern (~seq)))


  (define-syntax-class tych-rule
    (pattern [expr-patn in:tag⇐ ...
                        :≫
                        premise:tych-premise ...
                        :----
                        concl:tych-conclusion]
             #:with norm
             #'[expr-patn
                #:with (in.expr ...) (get-props this-syntax
                                                '(in.key ...))
                concl.pre ...
                premise.norm ... ...
                (parameterize ([current-rule-input-keys '(in.key ...)])
                  concl.result)]))

  (define-splicing-syntax-class tych-premise
    (pattern dir:stxparse-dir
             #:with [norm ...] #'dir))

  (define-syntax-class tych-conclusion
    (pattern [:≻ template]
             #:with [pre ...] #'[]
             #:with result
             #'(transfer-props #`template
                               this-syntax
                               (current-rule-input-keys)))

    (pattern [:⊢ template
                 out:tag⇒ ...]
             #:with [pre ...]
             (cond
               [(expected-output-list-key)
                #`[#:when (set=? (or (syntax-property this-syntax
                                                      '#,(expected-output-list-key))
                                     '())
                                 '(out.key ...))]]
               [else
                #'[]])
             #:with result
             #'(put-props #`template
                          '(out.key ...)
                          (list #`out.expr ...))))

  )



; phase 0 utilities

(define current-rule-input-keys
  (make-parameter '()))

(define (get-props stx keys)
  (let/ec break
    (for/list ([key (in-list keys)])
      (or (syntax-property stx key)
          (break #f)))))

(define (put-props stx keys vals)
  (foldl (lambda (k v s)
           (syntax-property s k v))
         stx keys vals))

(define (transfer-props dst src keys)
  (put-props dst keys (get-props src keys)))




(define-syntax syntax-parse/typecheck
  (syntax-parser
    [(_ stx-expr
        (~and (~seq option ...) :stxparse-options)
        rule:tych-rule ...)
     #'(syntax-parse stx-expr
         option ...
         rule.norm ...)]))




(begin-for-syntax
  [expected-output-list-key #f])

(syntax-parse/typecheck
 #'foo
  [pat (⇐ i _) ≫
      #:with out #'bar
      --------
      [⊢ out (⇒ y 3)]]

 [pat ≫
  --------
  [⊢ sadness]])






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
