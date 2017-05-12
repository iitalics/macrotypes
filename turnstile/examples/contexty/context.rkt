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


  (define the-context (make-parameter '()))

  (define (set-context! to)
    [the-context to])

  (define (context-before-pred p)
    (match (dropf (the-context) (negate p))
      [(cons _ xs) xs]
      [y y]))

  (define (context-after-pred p)
    (takef (the-context) (negate p)))



  (define-syntax context-before
    (syntax-parser
      [(_ patn)
       #'(context-before-pred (syntax-parser [patn #t] [_ #f]))]))

  (define-syntax context-after
    (syntax-parser
      [(_ patn)
       #'(context-after-pred (syntax-parser [patn #t] [_ #f]))]))

  (define-syntax context-push!
    (syntax-parser
      [(_ expr ...)
       #'(set-context! (append (reverse (list ((current-type-eval) expr) ...))
                               (the-context)))]))

  (define-syntax context-replace!
    (syntax-parser
      [(_ patn expr ...)
       #'(let ([p (syntax-parser [patn #t] [_ #f])])
           (set-context! (append (context-after-pred p)
                                 (reverse (list ((current-type-eval) expr) ...))
                                 (context-before-pred p))))]))

  (define-syntax context-pop-until!
    (syntax-parser
      [(_ patn)
       #'(set-context! (context-before patn))]))


  )
