#lang turnstile

; primitives
(define-base-types Unit Int Bool Str)

; unrestricted
(define-type-constructor -> #:arity >= 1)
(define-type-constructor × #:arity > 1)

; linear
(define-type-constructor -o #:arity >= 1)
(define-type-constructor ⊗ #:arity > 1)
(define-base-type Loc)
(define-type-constructor Box #:arity = 1)


(begin-for-syntax
  (require syntax/id-set)

  ; put multiple syntax properties onto the given syntax object
  ; (put-props stx key1 val1 key2 val2 ...) -> stx-
  (define-syntax (put-props stx)
    (syntax-case stx ()
      [(_ expr key val . rst)
       #'(put-props (syntax-property expr key val) . rst)]
      [(_ expr)
       #'expr]))

  ;; symmetric difference implementation, because current impl for
  ;; id-tables is bugged
  (define (sym-dif s1 s2)
    (for/fold ([s s1])
              ([x (in-set s2)])
      (if (free-id-set-member? s x)
          (free-id-set-remove s x)
          (free-id-set-add s x))))


  ; parameter to be set while expanding code that is in the linear
  ; sublanguage (within a (lin ...) form)
  (define linear-sublanguage?
    (make-parameter #f))

  ;;;; In the "linear sublanguage", you can attach to an output type the
  ;;;; property #%var, which contains a set of the variables (notation: V)
  ;;;; used by the expression that produced that type. You can retrieve
  ;;;; the set safely using (var-set #'σ) or put a new set using (+var-set #'σ V).
  ;;;; Operations on these sets are prefixed with lin/, e.g. lin/seq and lin/introduce.
  ;;;; A type with a set attached to it is usually notated σ+ as opposed to just σ.

  ;; THOUGHTS
  ;; I'm not sure if this is the best way to accomplish this. In the other linear language
  ;; I had two outputs on each rule: (⇒ : τ) for types and (⇒ % A) for variable usage.
  ;; The annoying thing about that is the problems arising when you want to declare/define
  ;; things and you have to attach something as a % property, or else try to deal with the #f
  ;; property that you risk passing into (current-type-eval). However if you look at this code,
  ;; the version with (⇒ % A) is MUCH more clear and simple than this version. Perhaps I can figure
  ;; a way to tame the #f properties and revert back to that.
  ;; However I'm very convinced that doing either way is a much better strategy than trying to
  ;; split / modify / observe contexts since this way you have much more control than you would
  ;; otherwise. Of course basically every other example of linear typing uses context splitting
  ;; and/or the algorithmic input/output context approach, so this method is technically not proven
  ;; to be sound etc.



  ; is the given type unrestricted?
  (define unrestricted?
    (syntax-parser
      [(~or ~Unit ~Int ~Bool ~Str) #t]
      [(~-> τ ...) (andmap unrestricted? (syntax-e #'(τ ...)))]
      [(~× τ ...)  (andmap unrestricted? (syntax-e #'(τ ...)))]
      [_ #f]))

  ; convert an unrestricted type to a linear type (shallow, only affects type
  ; constructor)
  (define (->linear ty)
    (syntax-parse ty
      [(~-> τ ...) ((current-type-eval) (syntax/loc ty (-o τ ...)))]
      [(~× τ ...)  ((current-type-eval) (syntax/loc ty (⊗ τ ...)))]
      [_ ty]))

  ; attempt to convert a linear type into an unrestricted type.
  ; if (unrestricted? tyl) is #f, where tyl is the result of this function, then
  ; the type could not be converted (e.g. if it contains the (Box _) type)
  (define (->unrestricted ty)
    (syntax-parse ty
      [(~-o σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (-> τ ...)))]
      [(~-> σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (-> τ ...)))]
      [(~⊗ σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (× τ ...)))]
      [(~× σ ...)
       #:with (τ ...) (stx-map ->unrestricted #'(σ ...))
       ((current-type-eval) (syntax/loc ty (× τ ...)))]
      [_ ty]))




  ; returns a set containing no variables
  (define (empty-var-set)
    (immutable-free-id-set))

  ; gets the variable set attached to a type (or empty if none attached)
  (define (var-set ty)
    (or (syntax-property ty '#%vars)
        (empty-var-set)))

  ; attach the variable set V to the type ty
  (define (+var-set ty V)
    (syntax-property ty '#%vars V))

  ; attach a single variable to a type if the given type is linear,
  ; otherwise attach nothing. use this + lin/introduce whenever introducing
  ; new linear variables into a context, e.g.
  ;   #:with σ/x (+linear-var #'σ #'x)
  ;   [[x ≫ x- : σ/x] ⊢ e ≫ e- ⇒ σ_out]
  ;   #:with σ+ (+var+set #'σ_out
  ;                       (lin/introduce (list #'σ/x) #:in #'σ_out))
  (define (+linear-var ty src)
    (cond
      [(unrestricted? ty)
       (+var-set ty (empty-var-set))]
      [else
       (let ([id (put-props (generate-temporary src)
                            'orig src)])
         ; NOTE: id does NOT BECOME REAL SYNTAX
         ;       it's just used to keep track of a linear variable's usage
         ;       i'm essentially just using free-id-set's because racket has
         ;       pretty weak hash-table operations (e.g. intersect, union)
         ;       compared to sets
         (+var-set ty (immutable-free-id-set (list id))))]))



  ; combine a list of variable sets as if they result from seperately
  ; evaluated expression that need to be sequenced. this means that any
  ; variables used twice will cause an error.
  (define (lin/seq Vs)
    (for/fold ([acc (empty-var-set)])
              ([V (in-list Vs)])
      (for ([v (in-set (set-intersect V acc))])
        (raise-syntax-error #f
                            "linear variable used more than once"
                            (syntax-property v 'orig)))
      (set-union V acc)))

  ; introduce all variables in Vs into the variable set V-body, meaning
  ; that an error will occur if any variables in any of Vs are not used in V-body.
  (define (lin/introduce Vs #:in V-body)
    (let ([V-new (foldl set-union (empty-var-set) Vs)])
      (for ([v (in-set (set-subtract V-new V-body))])
        (raise-syntax-error #f
                            "linear variable unused"
                            (syntax-property v 'orig)))
      (set-subtract V-body V-new)))

  ; merge to variable sets that should be equivalent, e.g. in the results of
  ; branching expressions.
  (define (lin/join V1 V2)
    (for ([v (in-set (sym-diff V1 V2))])
      (raise-syntax-error #f
                          "linear variable may be unused"
                          (syntax-property v 'orig)))
    V1)



  )



(provide (type-out Unit Int Bool Str -> × -o ⊗ Box)
         #%datum
         tup
         let let*
         lin
         share
         #%module-begin
         (rename-out [top-interaction #%top-interaction]))





; typed syntax

(define-typed-syntax (top-interaction . e) ≫
  [⊢ e ≫ e- ⇒ σ]
  --------
  [≻ (#%app- printf- "~s : ~a\n"
             e-
             '#,(type->str #'σ))])


(define-typed-syntax #%datum
  [(_ . k:exact-integer) ≫
   --------
   [⊢ 'k ⇒ Int]]
  [(_ . k:boolean) ≫
   --------
   [⊢ 'k ⇒ Bool]]
  [(_ . k:str) ≫
   --------
   [⊢ 'k ⇒ Str]])



(define-typed-syntax tup
  [(_ e ...) ≫
   #:when [linear-sublanguage?]
   #:when (> (stx-length #'(e ...)) 1)
   [⊢ e ≫ e- ⇒ σ] ...
   #:with σ_tup #'(⊗ σ ...)
   #:with σ_tup+ (let ([Vs (map var-set (syntax-e #'(σ ...)))])
                   (+var-set #'σ_tup (lin/seq Vs)))
   --------
   [⊢ (#%app- list- e- ...) ⇒ σ_tup+]]

  ;;; [unrestricted]
  [(_ e ... ) ≫
   #:when (not [linear-sublanguage?])
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (#%app- list- e- ...) ⇒ (× τ ...)]])



(define-typed-syntax let
  [(_ ([x:id rhs] ...) e) ≫
   #:when [linear-sublanguage?]
   [⊢ rhs ≫ rhs- ⇒ σ] ...
   #:with (σ/x ...) (stx-map +linear-var
                             #'(σ ...) #'(x ...))
   [[x ≫ x- : σ/x] ... ⊢ e ≫ e- ⇒ σ_out]
   #:with σ_out+ (let ([Vs-rhs (map var-set (syntax-e #'(σ ...)))]
                       [Vs-vars (map var-set (syntax-e #'(σ/x ...)))]
                       [V-out (var-set #'σ_out)])
                   (+var-set #'σ_out
                             (lin/seq (cons (lin/introduce Vs-vars #:in V-out)
                                            Vs-rhs))))
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out+]]

  ;;; [unrestricted]
  [(_ ([x:id rhs] ...) e) ≫
   #:when (not [linear-sublanguage?])
   [⊢ rhs ≫ rhs- ⇒ τ] ...
   [[x ≫ x- : τ] ... ⊢ e ≫ e- ⇒ τ_out]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ τ_out]])



(define-typed-syntax let*
  [(_ ([(x:id y:id) rhs]) e) ≫
   #:when [linear-sublanguage?]
   [⊢ rhs ≫ rhs- ⇒ σ]
   #:with (~or (~⊗ σ1 σ2) (~post (~fail (format "cannot destructure non-pair type: ~a"
                                                (type->str #'σ)))))
          (->linear #'σ)
   #:with σ/x (+linear-var #'σ1 #'x)
   #:with σ/y (+linear-var #'σ2 #'y)

   [[x ≫ x- : σ/x] [y ≫ y- : σ/y] ⊢ e ≫ e- ⇒ σ_out]
   #:with σ_out+ (let ([V-rhs (var-set #'σ)]
                       [V-x (var-set #'σ/x)]
                       [V-y (var-set #'σ/y)]
                       [V-out (var-set #'σ_out)])
                   (+var-set #'σ_out
                             (lin/seq
                              (list V-rhs (lin/introduce (list V-x V-y)
                                                         #:in V-out)))))
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (let- ([tmp rhs-])
            (let- ([x- (#%app- car tmp)]
                   [y- (#%app- cadr tmp)])
                  e-))
      ⇒ σ_out+]]

  ;;; [unrestricted]
  [(_ ([(x:id y:id) rhs]) e) ≫
   #:when (not [linear-sublanguage?])
   [⊢ rhs ≫ rhs- ⇒ τ]
   #:with (~or (~× τ1 τ2) (~post (~fail (format "cannot destructure non-pair type: ~a"
                                                (type->str #'τ)))))
   #'τ

   [[x ≫ x- : τ1] [y ≫ y- : τ2] ⊢ e ≫ e- ⇒ τ_out]
   #:with tmp (generate-temporary #'rhs)
   --------
   [⊢ (let- ([tmp rhs-])
            (let- ([x- (#%app- car tmp)]
                   [y- (#%app- cadr tmp)])
                  e-))
      ⇒ τ_out]]


  [(_ () e) ≫
   --------
   [≻ e]]
  [(_ ([x:id r] vs ...) e) ≫
   --------
   [≻ (let ([x r]) (let* (vs ...) e))]]
  [(_ ([(x:id y:id) r] vs ...+) e) ≫
   --------
   [≻ (let* ([(x y) r]) (let* (vs ...) e))]])




(define-typed-syntax lin
  [(_ _) ≫
   #:when [linear-sublanguage?]
   --------
   [#:error "cannot use 'lin' within linear language"]]

  [(_ lin-expr) ≫
   #:when (not [linear-sublanguage?])
   #:with (e- σ)
   (parameterize ([linear-sublanguage? #t])
     (syntax-parse #'lin-expr
       [(~and e [~⊢ e ≫ e- ⇒ σ])
        #'(e- σ)]))

   #:fail-unless (unrestricted? #'σ)
   (format "linear type ~a cannot leave linear boundary"
           (type->str #'σ))
   --------
   [⊢ e- ⇒ σ]])



(define-typed-syntax share
  [(_ e) ≫
   #:when [linear-sublanguage?]
   [⊢ e ≫ e- ⇒ σ]
   #:with τ (->unrestricted #'σ)
   #:fail-unless (unrestricted? #'τ)
   (format "cannot share type ~a" (type->str #'τ))
   #:with τ+ (+var-set #'τ (var-set #'σ))
   --------
   [⊢ e- ⇒ τ+]]

  [(_ _) ≫
   #:when (not [linear-sublanguage?])
   --------
   [#:error "cannot use 'share' outside of linear language"]])
