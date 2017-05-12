#lang racket
(require macrotypes/typecheck
         "../../contexty/context.rkt")

(define-base-type A)
(define-base-type B)
(define-base-type C)
(define-base-type D)
(define-base-type E)

(begin-for-syntax
  (require racket/base
           rackunit)


  (context-push! #'A #'B)
  (context-push! #'C #'D)

  (check-true (syntax-parse (the-context)
                [(~D ~C ~B ~A) #t]
                [_ #f]))


  (check-true (syntax-parse (context-before ~C)
                [(~B ~A) #t]
                [_ #f]))

  (check-true (syntax-parse (context-before ~E)
                [() #t]
                [_ #f]))

  (check-true (syntax-parse (context-after ~E)
                [(~D ~C ~B ~A) #t]
                [_ #f]))

  (context-replace! ~C #'E #'A)
  (check-true (syntax-parse (the-context)
                [(~D ~A ~E ~B ~A) #t]
                [_ #f]))

  )
