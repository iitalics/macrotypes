#lang racket
(require turnstile
         (for-syntax racket
                     syntax/parse))


(provide (rename-out [mod-begin #%module-begin]
                     [top #%top-interaction])
         unit)


(define-base-type Unit)

(begin-for-syntax
  (define prop syntax-property)
  (define (attach s . l)
    (let trav ([s s] [l l])
      (match l
        [(list* k v l-rest)
         (trav (syntax-property s k v)
               l-rest)]
        [(list) s])))

  (define (lexpand s . l)
    (local-expand (apply attach (cons s l))
                  'expression
                  '()))

  (define (eval-type s)
    ((current-type-eval) s))

  )



(define-syntax mod-begin
  (syntax-parser
    [(_ ...) #'(#%module-begin)]))



(define-syntax top
  (syntax-parser
    [(_ . e)
     #:with e- (lexpand #'e 'ctx⇐ '())
     #:with Γ- (prop #'e- 'ctx⇒)
     #:with τ (prop #'e- 'ty⇒)
     #'(printf "~a : ~a\nΓ = ~s\n"
               e-
               'τ
               'Γ-)]))



(define-syntax unit
  (syntax-parser
    [(_)
     #:with Γ (prop this-syntax 'ctx⇐)
     #:attr in (prop this-syntax '⇐) #:when (attribute in)
     #:fail-unless (Unit? #'in) "expected Unit type"
     (attach #'null
             'ctx⇒ #'Γ)]

    [(_)
     #:with Γ (prop this-syntax 'ctx⇐)
     (attach #'null
             'ty⇒ (eval-type #'Unit)
             'ctx⇒ #'Γ)]))
