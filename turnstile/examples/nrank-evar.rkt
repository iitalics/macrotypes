#lang racket
(require turnstile)
(provide (type-out Evar)
         (for-syntax mk-evar
                     Evar=?
                     evar-subst))


; the one "argument" to an Evar is a mk-type'd quoted symbol
; used to differentiate them
(define-type-constructor Evar #:arity = 1)

(begin-for-syntax
  ; generates a new evar
  (define (mk-evar [src #f])
    (define uniq-sym (gensym (syntax-parse src
                               [(~Evar (_ s)) (substring (symbol->string (syntax-e #'s))
                                                         0 3)]
                               [x:id (syntax-e #'x)]
                               [_ 'E])))
    (with-syntax ([quot-sym (mk-type #`(quote #,uniq-sym))])
      ((current-type-eval) #'(Evar quot-sym))))

  ; returns #t if both types are the same evars
  (define (Evar=? t1 t2)
    (syntax-parse (list t1 t2)
      [((~Evar ((~literal quote) s1))
        (~Evar ((~literal quote) s2)))
       (symbol=? (syntax-e #'s1)
                 (syntax-e #'s2))]
      [_ #f]))

  ; substitute evar e -> u in t
  (define (evar-subst e u t)
    (syntax-parse t
      [(~and e2 (~Evar _))
       #:when (Evar=? e #'e2)
       (transfer-stx-props u (merge-type-tags (syntax-track-origin u t #'evar-subst)))]
      [(esub ...)
       #:with res (stx-map (λ (t1) (evar-subst e u t1)) #'(esub ...))
       (transfer-stx-props #'res t #:ctx t)]
      [_ t]))

  )
