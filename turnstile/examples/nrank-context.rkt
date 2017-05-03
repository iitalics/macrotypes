#lang racket
(require (for-template turnstile
                       "nrank-evar.rkt"))
(provide (all-defined-out))

; a ContextElem (ce) is one of:
;  (ctx-tv id)       (identifier? id)
;  (ctx-ev ev)       (Evar? ev)
;  (ctx-ev= ev ty)   (and (Evar? ev) (type? ty))
;  (ctx-mark)

; This roughly corresponds to the Γ definition in the paper,
; with the difference that the "x:A" and "▹a" forms are condenced
; into just (ctx-mark), where eq? is used to find the specific mark

(struct ctx-tv (id) #:transparent)
(struct ctx-ev (ev) #:transparent)
(struct ctx-ev= (ev ty) #:transparent)
(struct ctx-mark (desc))

; contract for ctx-tv's that contain the same bound identifier
(define (ctx-tv/c id)
  (match-lambda
    [(ctx-tv id2) (type=? id id2)]
    [_ #f]))

; contract for ctx-ev's that contain the same Evar
(define (ctx-ev/c ev)
  (match-lambda
    [(ctx-ev ev2) (Evar=? ev ev2)]
    [_ #f]))

; contract for picking specific ctx-mark's
(define (ctx-mark/c cm)
  (lambda (c) (eq? c cm)))


; a Context (ctx) is a (box l/ce) where l/ce is a list of ContextElem's

; current computed context
(define current-ctx (make-parameter (box '())))

; context utility functions
(define (mk-ctx* . lst) (box lst))
(define (ctx-find p [ctx (current-ctx)])
  (findf p (unbox ctx)))
(define (ctx-cons ce [ctx (current-ctx)])
  (box (cons ce (unbox ctx))))
(define (ctx-cons! ce [ctx (current-ctx)])
  (set-box! ctx (cons ce (unbox ctx))))
(define (ctx-append! ces [ctx (current-ctx)])
  (set-box! ctx (append ces (unbox ctx))))

; calls fn such that any affects to ctx will be applied
; in the space instead of the first found element that
; matches predicate 'p'.
(define (call-between ctx p fn)
  (let-values ([(a b) (splitf-at (unbox ctx)
                                 (negate p))])
    (set-box! ctx (cdr b))
    (begin0 (fn)
      (ctx-append! a ctx))))

; get parts of a context before/after the first (latest) element that
; maches the given predicate
(define (get-before ctx p)
  (match (dropf (unbox ctx) (negate p))
    [(cons _ xs) xs]
    [_ '()]))
(define (get-after ctx p)
  (takef (unbox ctx) (negate p)))


; removes elements from the given context until it finds one that
; matches the given predicate (which it removes as well). returns
; the list of elements popped, excluding the element that matched
; the predicate.
(define (ctx-pop-until! p [ctx (current-ctx)])
  (let trav ([lst (unbox ctx)] [acc '()])
    (match lst
      ['()
       (set-box! ctx '()) acc]
      [(cons (? p) rst)
       (set-box! ctx rst) (reverse acc)]
      [(cons elem rst)
       (trav rst (cons elem acc))])))


; applies all ctx-ev= substitutions in the context to the given type.
(define (subst-from-ctx t [ctx (current-ctx)])
  (let trav ([t t] [lst (unbox ctx)])
    (match lst
      ['() t]
      [(cons (ctx-ev= e u) rst)
       (trav (evar-subst e u t) rst)]
      [(cons _ rst)
       (trav t rst)])))
