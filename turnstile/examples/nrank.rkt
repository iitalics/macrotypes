#lang racket
(require turnstile
         (for-syntax racket
                     rackunit))

; fundamental types
(define-base-types Unit)
(define-type-constructor → #:arity = 2)
(define-binding-type All #:bvs = 1 #:arity = 1)

; the one "argument" to an Evar is a mk-type'd quoted symbol
; used to differentiate them
(define-type-constructor Evar #:arity = 1)

(begin-for-syntax

  ; generates a new evar
  (define (mk-evar [src #f])
    (define uniq-sym (gensym (syntax-parse src
                               [x:id (syntax-e #'x)]
                               [_ 'E])))
    (with-syntax ([quot-sym (mk-type #`(quote #,uniq-sym))])
      ((current-type-eval) #'(Evar quot-sym))))

  ; returns #t if both types are the same evars
  (define (Evar=? T1 T2)
    (syntax-parse (list T1 T2)
      [((~Evar ((~literal quote) s1))
        (~Evar ((~literal quote) s2)))
       (symbol=? (syntax-e #'s1)
                 (syntax-e #'s2))]
      [_ #f]))


  ; a ContextElem (ctx-elem) is one of:
  ;  (ctx-tv id)       (identifier? id)
  ;  (ctx-ev ev)       (Evar? ev)
  ;  (ctx-ev= ev ty)   (and (Evar? ev) (type? ty))
  ;  (ctx-mark)

  ; This roughly corresponds to the Γ definition in the paper,
  ; with the difference that the "x:A" and "▹a" forms are condenced
  ; into just (ctx-mark), where eq? is used to find the specific mark

  (struct ctx-tv (id))
  (struct ctx-ev (ev))
  (struct ctx-ev= (ev ty))
  (struct ctx-mark (sym))

  ; contract for ctx-tv's that contain the same bound identifier
  (define (ctx-tv/c id)
    (match-lambda
      [(ctx-tv id2) (bound-identifier=? id id2)]
      [_ #f]))

  ; contract for ctx-ev's that contain the same Evar
  (define (ctx-ev/c ev)
    (match-lambda
      [(ctx-ev ev2) (Evar=? ev ev2)]
      [_ #f]))


  ; a Context (ctx) is a (box l/ce) where l/ce is a list of ContextElem's

  ; current computed context
  (define current-ctx (make-parameter (box '())))


  ; removes elements from the context until the element specified
  ; by the predicate is found. returns the matching element, or #f
  ; if not found.
  (define (ctx-pop! predicate [ctx (current-ctx)])
    #f)

  )
