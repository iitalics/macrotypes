#lang racket
(require macrotypes/typecheck
         syntax/parse)


(define-syntax syntax-parse/typecheck
  (syntax-parser
    [(_ stx _ ...)
     #'(let ([the-stx stx])
         (syntax-parse the-stx
           [_ (raise-syntax-error 'syntax-parse/typecheck "unimplemented"
                                  the-stx)]))]))


#;(define-syntax (foo stx)
  (syntax-parse/typecheck
   stx
   [(main-pat ...) (⇐ in1 pat1) ... ≫
    [[x-templ ≫ x-patn : τ1] ooo
     ⊢
     e-templ ≫ e-patn (⇐ e-in1 templ1) ... (⇒ e-out1 pat1) ...]
    ooo
    #:stx-parse-dir ...
    --------
    [⊢ main-templ
       (⇒ out1 templ1) ...]
    ]
   ...))

#|
SYNTAX:
(syntax-parse/typecheck
  <id>
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
