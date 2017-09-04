#lang racket
(provide (all-defined-out))

;; a term in linear logic
(struct term () #:transparent
  #:methods gen:custom-write
  [(define (write-proc t p m) (custom-write-term t p m))])
;;   unique object
(struct unique term (name id) #:transparent)
;;   predicate (compound object)
(struct predicate term (name id args) #:transparent)
;;   logical combinators
(struct ⊗ term (x y) #:transparent)
(struct one term () #:transparent)
;; TODO: ⊕

;; a rule (in -o out), parameterized with variables
(struct rule (vars in out)
  #:methods gen:custom-write
  [(define (write-proc r p m) (custom-write-rule r p m))])

;; a stage is a collection of rules (hash symbol? => rule?)
(struct stage (name rules) #:transparent
  #:methods gen:custom-write
  [(define (write-proc s p m) (custom-write-stage s p m))])

;; a type (not used much currently)
(struct type ())

;; fold into repeated binary application
;; e.g. (⊗* a b c) ≡ (⊗ a (⊗ b c))
(define (⊗* . l)
  (match l
    ['() (one)]
    [(list as ... b) (foldr ⊗ b as)]))


(define (custom-write-term trm port mode)
  (match trm
    [(unique N _)
     (display N port)]
    [(predicate N _ ts)
     (display (list* N (map ~v ts)) port)]
    [(⊗ a b)
     (display (list '* (~v a) (~v b)) port)]
    [(one) (display "1" port)]))

(define (custom-write-rule rul port mode)
  (fprintf port "[~a] ~a -o ~a"
           (string-join (map ~a (rule-vars rul)) " ")
           (rule-in rul) (rule-out rul)))

(define (custom-write-stage stg port mode)
  (display (list* 'stage (stage-name stg)
                  (map list
                       (hash-keys (stage-rules stg))
                       (hash-values (stage-rules stg))))
           port))


;; rule-satisfy : rule? term? -> (or/c #f (listof term?))
;;
;; attempt to satisfy the given rule with the given context.
;; if satisfiable, returns a (cons ctx' in'), where ctx' = new
;; context with the rule applied, and in' = rule input substituted
;; with appropriate arguments.
;; otherwise, returns #f.
(define (rule-apply rul ctx)

  ;; sat : trm inp subs -> (list (cons trm' subs) ...)
  (define (sat trm inp subs)
    (match inp
      [(one)
       (list (cons trm subs))]

      [(⊗ a b)
       (for*/list ([r  (in-list (sat trm     a subs))]
                   [r+ (in-list (sat (car r) b (cdr r)))])
         r+)]

      [(predicate _ i rhs)
       (find trm i rhs subs)]))

  ;; find : trm pred-id (list rh-trm ...) subs -> (list (cons trm' subs) ...)
  (define (find trm i rhs subs)
    (match trm
      [(one) '()]

      [(⊗ a b)
       (append
        (map (λ (r) (cons (⊗ (car r) b) (cdr r)))
             (find a i rhs subs))
        (map (λ (r) (cons (⊗ a (car r)) (cdr r)))
             (find b i rhs subs)))]

      [(predicate _ j lhs)
       (cond
         [(and (eq? i j)
               (unify* lhs rhs subs))
          => (λ (subs)
               (list (cons (one) subs)))]

         [else '()])]))

  ;; unify : unique sym/unique subs -> (or #f subs)
  (define (unify lh rh subs)
    (match (hash-ref subs rh rh)
      [(? symbol?) (hash-set subs rh lh)]
      [(== lh) subs]
      [_ #f]))

  ;; unify* : (listof unique) (listof sym/unique) subs -> (or #f subs)
  (define (unify* lhs rhs subs)
    (for/fold ([subs subs])
              ([lh (in-list lhs)]
               [rh (in-list rhs)]
               #:break (not subs))
      (unify lh rh subs)))

  ;; apply substitution to term
  (define (unsub trm subs)
    (match trm
      [(⊗ a b) (⊗ (unsub a subs) (unsub b subs))]

      [(predicate X i args)
       (predicate X i (map (λ (t) (unsub t subs)) args))]

      [(? symbol? x)
       (hash-ref subs x one)]

      [_ trm]))

  (map (λ (r)
         (let* ([ctx- (car r)]
                [subs (cdr r)]
                [out- (unsub (rule-out rul) subs)])
           (cons (⊗ ctx- out-)
                 (map (λ (x) (hash-ref subs x))
                      (rule-vars rul)))))
       (sat ctx (rule-in rul) #hash())))



(define (interactive ctx stg)
  (let/ec esc
    (for/fold ([ctx ctx])
              ([_ (in-producer void)])

      ;; early exit
      (define (finish)
        (printf "final state: ~a\n" ctx)
        (esc))

      ;; (list (list name in new-ctx) ...)
      (define opts
        (remove-duplicates
         #:key (λ (o) (cons (first o) (second o)))
         (for*/list ([(rule-name rul) (in-hash (stage-rules stg))]
                     [r (in-list (rule-apply rul ctx))])
           (list rule-name
                 (cdr r)
                 (car r)))))

      (when (empty? opts)
        (printf "no transitions!\n")
        (finish))

      (display "0] quit\n")
      (for ([o (in-list opts)]
            [i (in-naturals 1)])
        (printf "~a] ~a\n"
                i
                (cons (first o) (second o))))

      (display "?- ")
      (flush-output)
      (define choice
        (or (for/or ([c (in-port)])
              (cond
                [(zero? c) (finish)]

                [(and (exact-integer? c)
                      (<= 0 c (length opts)))
                 (list-ref opts (sub1 c))]

                [else
                 (and (printf "invalid index!\n") #f)]))
            (finish)))

      (third choice))))







(module+ test
  (require rackunit)

  (define (mk-block [name "<unnamed>"])
    (unique name 'BLOCK))

  (define (clear x)
    (predicate "clear" 'CLEAR (list x)))
  (define (on x y)
    (predicate "on" 'ON (list x y)))

  (define unstack
    (rule '(x y)
          (on 'x 'y)
          (⊗ (clear 'x) (clear 'y))))

  (define A (mk-block "A"))
  (define B (mk-block "B"))
  (check-equal? (rule-apply unstack (on A B))
                (list (list (⊗ (one) (⊗ (clear A) (clear B)))
                            A B)))

  (check-equal? (rule-apply unstack (⊗ (one) (one)))
                '())

  )
