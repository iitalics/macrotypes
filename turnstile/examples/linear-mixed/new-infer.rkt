#lang racket

(require (for-template (except-in macrotypes/typecheck #%module-begin))
         syntax/parse
         syntax/stx)

(provide new-infer
         DEFAULT-VAR
         DEFAULT-TYPEVAR
         ~new-typecheck)


(define (new-infer es
                   #:tvctx [tvctx '()]
                   #:ctx [ctx '()]
                   #:tag [tag (current-tag)]
                   #:expa [expa expand/df]
                   #:tev [tev #'(current-type-eval)]
                   #:kev [kev #'(current-type-eval)]
                   #:var-stx [var-stxs (var-transformers-for-context ctx tag tev kev)])
  (syntax-parse es
    [(e ...)
     #:with ((~or (X:id X-stx)
                  ([x:id . _] x-stx)) ...)
     (stx-map list ctx var-stxs)
     #:with (~or ([tv:id (~seq tvsep:id tvk) ...] ...)
                 (~and (tv:id ...)
                       (~parse ([(tvsep ...) (tvk ...)] ...)
                               (stx-map (λ _ #'[(::) (#%type)]) #'(tv ...)))))
     tvctx
     #:with ((~literal #%plain-lambda) tvs+
             (~let*-syntax
              ((~literal #%expression)
               ((~literal #%plain-lambda) xs+
                (~let*-syntax
                 ((~literal #%expression) e+) ... (~literal void))))))
     (expa
      #`(λ (tv ...)
          (let*-syntax ([tv (make-rename-transformer ; TODO: make this an argument too?
                             (mk-tyvar
                              (attachs #'tv '(tvsep ...) #'(tvk ...)
                                       #:ev #,kev)))] ...)
                       (λ (X ... x ...) ; TODO: not this, the order of the ctx gets screwed up and
                         ; impossible to pattern match on. either restore the order
                         ; later, to preserve weird backwards compat, or just don't
                         ; do this?? i don't see why turnstile should have to move
                         ; type vars to the front.
                         (let*-syntax ([X X-stx] ...
                                       [x x-stx] ...)
                                      (#%expression e) ... void)))))
     (list #'tvs+
           #'xs+
           #'(e+ ...)
           (stx-map (λ (e) (detach e tag)) #'(e+ ...)))]))

(define (var-transformers-for-context ctx tag tev kev)
  (stx-map (syntax-parser
             ; missing seperator
             [[x:id τ]
              #`(make-variable-like-transformer
                 (attach #'x '#,tag (#,tev #'τ)))]
             ; seperators given
             [[x:id (~seq sep:id τ) ...]
              #`(make-variable-like-transformer
                 (attachs #'x '(sep ...) #'(τ ...)
                          #:ev #,tev))]
             ; just variable; interpreted as type variable
             [X:id
              #`(make-variable-like-transformer
                 (mk-tyvar (attach #'X ':: (#,kev #'#%type))))])
           ctx))

(define-syntax DEFAULT-VAR
  (syntax-parser
    [(_ x (~seq tag prop) ...)
     #'(make-variable-like-transformer
        (attachs #'x '(tag ...) #'(prop ...)))]))

(define-syntax DEFAULT-TYPEVAR
  (syntax-parser
    [(_ x)
     #'(make-variable-like-transformer
        (mk-tyvar (attach #'x ':: ((current-type-eval) #'#%type))))]))



;; append two syntax lists together
;; (stx-append #'(x ...) #'(y ...)) = #'(x ... y ...)
; stx-append : (listof stx-elem) (listof stx-elem) -> (listof stx-elem)
(define (stx-append xs ys)
  (append (stx->list xs)
          (stx->list ys)))

;; flatten a list of trees (with fixed depth per tree given by each element of
;; the depths list) into a single list
; stx-flats : (listof depth) (listof stx-tree) -> (listof stx-elem)
(define (stx-flats ds ts)
  (define (flat d t)
    (cond
      [(stx-null? t) t]
      [(zero? d) (list t)]
      [else
       (stx-append (flat (sub1 d) (stx-car t))
                   (flat d        (stx-cdr t)))]))
  (with-syntax ([((x ...) ...) (stx-map flat ds ts)])
    #'[x ... ...]))

;; unflatten a list back into a list of trees, as if the list is a flattened version
;; of the tree (per stx-flats).
;; this is useful as a "delayed-map", where we need the tree as a list to easily map,
;; but then we need it back in tree-form for e.g. pattern matching with ellipsis
; stx-unflats : (listof depth) (listof stx-tree) (listof stx-elem) -> (listof stx-tree)
(define (stx-unflats ds orig lst)
  (define (next)
    (begin0 (stx-car lst)
      (set! lst (stx-cdr lst))))
  (define (unflat d t)
    (cond
      [(stx-null? t) t]
      [(zero? d) (next)]
      [else
       (cons (unflat (sub1 d) (stx-car t))
             (unflat d        (stx-cdr t)))]))
  (stx-map unflat ds orig))

;; map a tree shaped syntax that has a fixed depth d.
;; e.g. (stx-map/depth e id->upper #'(((a) (b c)) (() (d)))) = #'(((A) (B C)) (() (D)))
(define (stx-map/depth d f stx)
  (cond
    [(zero? d) (f stx)]
    [(stx-null? stx) stx]
    [else
     (cons (stx-map/depth (sub1 d) f (stx-car stx))
           (stx-map/depth d        f (stx-cdr stx)))]))


;; for testing:
(define (fake-infer es #:ctx ctx #:var-stx var-stxs)
  (define (stx->datum s)
    (syntax->datum (datum->syntax #f s)))
  (printf (string-append "es:       ~a\n"
                         "ctx:      ~a\n"
                         "var-stxs: ~a\n")
          (stx->datum es)
          (stx->datum ctx)
          (stx->datum var-stxs))
  (list '()
        (stx-map (syntax-parser
                   [(x . _) (format-id #'x "~a+" #'x)])
                 ctx)
        es
        '()))

(define (new-infer/depths vars/ctx/es
                          ctx-deps
                          es-deps)
  (syntax-parse vars/ctx/es
    [(vars ctx es)
     #:with (_ xs+/flat es+/flat _)
     (new-infer (stx-flats es-deps #'es)
                #:ctx (stx-flats ctx-deps #'ctx)
                #:var-stx (stx-flats ctx-deps #'vars))
     (list (stx-unflats ctx-deps #'ctx #'xs+/flat)
           (stx-unflats es-deps #'es #'es+/flat))]))

(define (new-infers/depths v/c/es
                           depth
                           ctx-deps
                           es-deps)
  (stx-map/depth depth
                 (λ (v/c/e)
                   (new-infer/depths v/c/e
                                     ctx-deps
                                     es-deps))
                 v/c/es))


(begin-for-syntax
  (require macrotypes/typecheck
           macrotypes/stx-utils
           (for-template racket/base
                         syntax/parse)
           racket/syntax
           syntax/parse
           syntax/stx)
  (provide (all-defined-out))

  (define-syntax-class dots
    (pattern (~datum ...)))

  ;; nest stx, suffixed with every element in ooos
  ;; e.g.
  ;;   (nest #'x #'(aaa bbb ccc)) = #'(((x aaa) bbb) ccc)
  (define (nested stx ooos)
    (cond
      [(stx-null? ooos) stx]
      [else (nested (datum->syntax stx (list stx (stx-car ooos)))
                    (stx-cdr ooos))]))

  ;;; premise
  (define-splicing-syntax-class ts/premise
    #:datum-literals (⊢)
    (pattern (~seq [a ... ⊢ ~! b ...] ooo:dots ...)
             #:with ctx:ts/ctx #'[a ...]
             #:with tc:ts/tc #'[b ...]
             #:with dep (stx-length #'[ooo ...])
             ; note: t- prefix means "template"
             ;       p- prefix means "pattern"
             #:with t-v/c/es (nested #'(ctx.t-vars ctx.t-ctx tc.t-es)
                                     #'[ooo ...])
             #:with p-xs/es (nested #'(ctx.pat tc.pat)
                                    #'[ooo ...])
             #:with pat
             #`(~post
                (~post
                 (~parse
                  p-xs/es (new-infers/depths #`t-v/c/es
                                             'dep
                                             '(ctx.deps ...)
                                             '(tc.deps ...)))))))


  ;;; context
  (define-syntax-class ts/ctx
    #:attributes ([deps 1] t-vars t-ctx pat)
    ; basically grouped contexts, but grouping is automatic
    (pattern [(~seq elem:ts/ctx-elem ooo:dots ...) ...]
             #:with (deps ...) (stx-map stx-length #'([ooo ...] ...))
             #:with t-ctx  (stx-map nested
                                    #'(elem.t-ctx-elem ...)
                                    #'([ooo ...] ...))
             #:with t-vars (stx-map nested
                                    #'(elem.t-var-stx ...)
                                    #'([ooo ...] ...))
             #:with pat    (stx-map nested
                                    #'(elem.pat ...)
                                    #'([ooo ...] ...)))
    ; (grouped) contexts
    (pattern [(elem:ts/ctx-elem ooo:dots ...) ...]
             #:with (deps ...) (stx-map stx-length #'([ooo ...] ...))
             #:with t-ctx  (stx-map nested
                                    #'(elem.t-ctx-elem ...)
                                    #'([ooo ...] ...))
             #:with t-vars (stx-map nested
                                    #'(elem.t-var-stx ...)
                                    #'([ooo ...] ...))
             #:with pat    (stx-map nested
                                    #'(elem.pat ...)
                                    #'([ooo ...] ...))))

  (define-syntax-class ts/ctx-elem
    #:datum-literals (≫)
    #:attributes (t-ctx-elem t-var-stx pat)
    ; custom variable syntax, e.g. [LINEAR x ≫ x- : t]
    (pattern [var-mac:id t-x:id ≫ pat . (~and props [(~seq tag prop) ...])]
             #:with t-ctx-elem #'(t-x . props)
             #:with t-var-stx #'(var-mac t-x . props))
    ; normal variable [x ≫ x- : t]
    (pattern [t-x:id ≫ pat . (~and props [(~seq tag prop) ...])]
             #:with t-ctx-elem #'(t-x . props)
             #:with t-var-stx #'(DEFAULT-VAR t-x . props))
    ; type variable X
    (pattern X:id
             #:with t-ctx-elem #'X
             #:with t-var-stx #'(DEFAULT-TYVAR X)
             #:with pat #'_))


  ;;; typing clause
  (define-syntax-class ts/tc
    #:attributes ([deps 1] t-es pat)
    (pattern [(~seq elem:ts/tc-elem ooo:dots ...) ...]
             #:with (deps ...) (stx-map stx-length #'([ooo ...] ...))
             #:with t-es (stx-map nested
                                  #'(elem.templ ...)
                                  #'([ooo ...] ...))
             #:with pat  (stx-map nested
                                  #'(elem.pat ...)
                                  #'([ooo ...] ...)))
    (pattern single:ts/tc-elem
             #:with (deps ...) '(0)
             #:with t-es #'(single.templ)
             #:with pat #'(single.pat)))

  (define-syntax-class ts/tc-elem
    #:datum-literals (≫ ⇒ ⇐)
    #:attributes (templ pat)
    ; TODO: modularize?
    (pattern [templ ≫ p-expa (⇒ tag p-prop) ...]
             #:with tmp (generate-temporary #'p-expa)
             #:with pat #'(~and tmp
                                p-expa
                                (~parse p-prop
                                        (detach #'tmp `tag)) ...))
    (pattern [templ ≫ p-expa ⇒ tag p-prop]
             #:with tmp (generate-temporary #'p-expa)
             #:with pat #'(~and tmp
                                p-expa
                                (~parse p-prop (detach #'tmp `tag))))
    (pattern [templ ≫ p-expa ⇒ p-type]
             #:with tmp (generate-temporary #'p-expa)
             #:with pat #`(~and tmp
                                p-expa
                                (~parse p-type (detach #'tmp ':))))
    (pattern [t-expr ≫ p-expa ⇐ t-type]
             #:with templ #'(add-expected t-expr t-type)
             #:with pat #'p-expa))

  )

(define-syntax ~new-typecheck
  (pattern-expander
   (syntax-parser
     [(_ p:ts/premise ...)
      #'(~and p.pat ...)])))
