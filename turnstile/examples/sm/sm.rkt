#lang racket
(require (for-syntax syntax/parse
                     racket/syntax
                     syntax/transformer)
         racket/stxparam
         racket/unsafe/ops)

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top-interaction #%top-interaction]
                     [@%datum #%datum]
                     [@define define]
                     [@begin do]
                     [@+ +] [@- -] [@* *] [@/ /] [@< <] [@> >] [@= =]
                     [@if if]
                     [@while while]
                     [@display .d]
                     [@show .s])
         dup drop swap)


(define-syntax-parameter stack
  (λ (stx)
    (raise-syntax-error #f "stack-var not set" stx)))

(define-syntax ==>
  (syntax-parser
    [(_ s-expr next-expr)
     #:with s (generate-temporary #'s-expr)
     #'(let ([s s-expr])
         (syntax-parameterize
             ([stack (make-rename-transformer #'s)])
           next-expr))]))

(define global-s
  (make-parameter '()))


(define-syntax @%module-begin
  (syntax-parser
    #:literals (@define)
    [(_ (@define ~! op:id inner-e ...) ...
        toplvl-e ...)

     #'(#%module-begin
        (define-op op
          #:func (λ (s) (@begin s inner-e ...)))
        ...

        (global-s (@begin (global-s) toplvl-e ...)))]))

(define-syntax @%top-interaction
  (syntax-parser
    [(_ . e)
     #'(global-s (==> (global-s) e))]))

(define-syntax @define
  (λ (stx)
    (raise-syntax-error #f "invalid use outside of toplevel" stx)))

(define-syntax @begin
  (syntax-parser
    [(_) #'stack]
    [(_ e) #'e]
    [(_ e0 e ...) #'(==> e0 (@begin e ...))]))

(define-syntax @%datum
  (syntax-parser
    [(_ . d) #'(cons 'd stack)]))

(define-syntax @if
  (syntax-parser
    [(_ [e1 ...]
        [e2 ...])
     #'(br- stack
            (λ (s1) (@begin s1 e1 ...))
            (λ (s2) (@begin s2 e2 ...)))]))

(define-syntax @while
  (syntax-parser
    [(_ [e1 ...] e2 ...)
     #'(let loop ([s stack])
         (br- (@begin s e1 ...)
              (λ (s-) (loop (@begin s- e2 ...)))
              values))]))

(define (br- s f g)
  (match s
    [(cons #t s-) (f s-)]
    [(cons #f s-) (g s-)]))


(define-syntax define-op
  (syntax-parser
    #:datum-literals (=> ->)
    [(_ name:id x ... => y ...)
     #:with name- (generate-temporary #'name)
     #:with (x* ...) (reverse (syntax->list #'[x ...]))
     #:with (y* ...) (reverse (syntax->list #'[y ...]))
     #'(begin
         (define/match (name- s)
           [[(list* x* ... s-)] (list* y* ... s-)])
         (define-op name #:func name-))]

    [(_ name:id #:func f)
     #'(define-syntax name
         (make-variable-like-transformer #'(f stack)))]

    [(_ name:id x ... -> f)
     #'(define-op name x ... => (f x ...))]))

(define-syntax-rule (define-ops [name . x/o] ...)
  (begin (define-op name . x/o) ...))

(define-ops
  [dup    x => x x]
  [drop   x => ]
  [swap   x y => y x]
  [@+     n m -> unsafe-fx+]
  [@-     n m -> unsafe-fx-]
  [@*     n m -> unsafe-fx*]
  [@/     n m -> unsafe-fxquotient]
  [@<     n m -> unsafe-fx<]
  [@>     n m -> unsafe-fx>]
  [@=     n m -> unsafe-fx=]
  [@display #:func (λ (s)
                     (displayln (car s))
                     (cdr s))]
  [@show #:func (λ (s)
                  (displayln (string-join
                              (for/fold ([z '()])
                                        ([x (in-list s)])
                                (cons (~a x) z))))
                  s)])
