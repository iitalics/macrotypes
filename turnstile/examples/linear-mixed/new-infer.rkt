#lang racket/base
(require turnstile)

(begin-for-syntax
  (require racket
           (for-syntax syntax/parse))
  (provide new-infer)


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
              (λ (X ... x ...)
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





  )
