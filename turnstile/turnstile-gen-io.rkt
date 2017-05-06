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

  (define-splicing-syntax-class key⇐
    (pattern (~seq :⇐ expr)
             #:with key (default-input-key))
    (pattern (:⇐ key expr)))

  (define-splicing-syntax-class key⇒
    (pattern (~seq :⇒ expr)
             #:with key (default-output-key))
    (pattern (:⇒ key expr)))

  (define-splicing-syntax-class ellipses
    (pattern (~seq (~literal ...)))
    (pattern (~seq)))



  (define-syntax-class tych-rule
    (pattern [expr-patn in:key⇐ ...
                        :≫
                        premise:tych-premise ...
                        :----
                        concl:tych-conclusion]
             #:with norm
             #'[expr-patn
                #:with (in.expr ...) (prop/inputs this-syntax
                                                  `(in.key ...))
                concl.pre ...
                premise.norm ... ...
                concl.result]))


  (define-splicing-syntax-class tych-premise
    (pattern dir:stxparse-dir
             #:with [norm ...] #'dir))

  (define-syntax-class tych-conclusion
    (pattern [:≻ expr]
             #:with (pre ...) #'()
             #:with result #'#`expr))

  )


(define (prop/inputs stx keys)
  (let/ec break
    (for/list ([key (in-list keys)])
      (or (syntax-property stx key)
          (break #f)))))


(define-syntax syntax-parse/typecheck
  (syntax-parser
    [(_ stx-expr
        (~and (~seq option ...) :stxparse-options)
        rule:tych-rule ...)
     #'(syntax-parse stx-expr
         option ...
         rule.norm ...)]))

(syntax-parse/typecheck
 'foo
 [pat ≫
  #:with out #'bar
  --------
  [≻ out]])







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
