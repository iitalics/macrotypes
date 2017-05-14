#lang racket
(require macrotypes/typecheck)

(begin-for-syntax
  (require racket/base
           racket/match
           (only-in racket/syntax generate-temporary)
           (only-in racket/function negate)
           (only-in racket/list takef dropf)
           syntax/parse
           (for-syntax syntax/parse))

  (provide (all-defined-out))


  ; parameter representing the global context (a list of types/markers)
  ; leftmost elements represent later entries, while rightmost elements represent older entries
  (define the-context (make-parameter '()))

  ; set the context to the given list
  (define (set-context! to)
    [the-context to])

  ; get every entry before the first element satisfying the predicate
  (define (context-before-pred p)
    (match (dropf (the-context) (negate p))
      [(cons _ xs) xs]
      [y y]))

  ; get every entry after the first element satisfying the predicate
  (define (context-after-pred p)
    (takef (the-context) (negate p)))



  ; (context-before <syntax-pattern>)
  ; like context-before, but takes in a syntax pattern instead of a predicate
  (define-syntax context-before
    (syntax-parser
      [(_ patn)
       #'(context-before-pred (syntax-parser [patn #t] [_ #f]))]))

  ; (context-after <syntax-pattern>)
  ; like context-after, but takes in a syntax pattern instead of a predicate
  (define-syntax context-after
    (syntax-parser
      [(_ patn)
       #'(context-after-pred (syntax-parser [patn #t] [_ #f]))]))

  ; (context-push! <expr> ...)
  ; adds the given expressions to the context in order (first argument is added,
  ; then second argument, etc.). applies current-type-eval to each argument
  (define-syntax context-push!
    (syntax-parser
      [(_ expr ...)
       #'(set-context! (append (reverse (list ((current-type-eval) expr) ...))
                               (the-context)))]))

  ; (context-replace! <syntax-pattern> <expr> ...)
  ; like context-push!, but adds entries in place of the first element that matches
  ; the given syntax pattern.
  (define-syntax context-replace!
    (syntax-parser
      [(_ patn expr ...)
       #'(let ([p (syntax-parser [patn #t] [_ #f])])
           (set-context! (append (context-after-pred p)
                                 (reverse (list ((current-type-eval) expr) ...))
                                 (context-before-pred p))))]))

  ; (context-pop-until! <syntax-pattern>)
  ; removes entries until it finds one matching the given syntax pattern. removes
  ; that entry as well.
  (define-syntax context-pop-until!
    (syntax-parser
      [(_ patn)
       #'(set-context! (context-before patn))]))

  )
