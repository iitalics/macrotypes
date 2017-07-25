#lang turnstile
(require (for-syntax "fabul-utils.rkt"))

(provide begin let let* letrec λ lambda #%app if tup cons nil
         drop match-list
         proj isnil head tail list-ref member
         L U
         #%module-begin #%top-interaction require
         (typed-out [= : (→ Int Int Int)]
                    [< : (→ Int Int Bool)]
                    [sub1 : (→ Int Int)]
                    [add1 : (→ Int Int)]
                    [zero? : (→ Int Bool)]))

; import other languages
(require (prefix-in U: "../ext-stlc.rkt")
         (prefix-in U: (except-in "../stlc+cons.rkt" tup proj))
         (prefix-in U: (only-in "../stlc+tup.rkt" tup proj))
         (prefix-in L: "lin.rkt")
         (prefix-in L: "lin+cons.rkt")
         (only-in "../ext-stlc.rkt" → ~→)
         (only-in "../stlc+tup.rkt" × ~×)
         (only-in "../stlc+cons.rkt" List ~List)
         (only-in "lin+cons.rkt" ⊗ ~⊗ MList ~MList)
         (only-in "lin+tup.rkt" gen-cad*rs)
         "lin.rkt" #| this includes base types like Int, Unit, etc. |#)

; reuse types
(reuse Unit Bool Int Float String → #:from "../ext-stlc.rkt")
(reuse × #:from "../stlc+tup.rkt")
(reuse List #:from "../stlc+cons.rkt")
(reuse -o ⊗ MList #:from "lin+cons.rkt")

; reuse forms
(reuse #%datum ann and or define-type-alias #:from "../ext-stlc.rkt")
(reuse define #:from "lin.rkt")



; dispatch some forms to L: or U: variant, based on [current-language]
(define-syntax language-dispatch
  (syntax-parser
    [(_ [lang ...] form)
     #:with (form/lang ...) (stx-map (λ (X) (format-id X "~a:~a" X #'form)) #'[lang ...])
     #'(define-syntax form
         (syntax-parser
           [(_ . args)
            #:when (eq? [current-language] 'lang)
            (syntax/loc this-syntax
              (form/lang . args))] ...
           [_
            (raise-syntax-error 'form
                                (format "form not allowed inside ~a language"
                                        (language-name)))]))]

    [(_ [lang ...] form ...+)
     #'(begin-
         (language-dispatch [lang ...] form) ...)]))

(language-dispatch [L U] begin let let* letrec λ lambda #%app if tup cons nil)
(language-dispatch [L] drop match-list)
(language-dispatch [U] proj isnil head tail list-ref member)


(begin-for-syntax
  (define (fully-unrestricted? type)
    (and (unrestricted-type? type)
         (syntax-parse type
           [(~Any _ τ ...) (for/and ([t (in-syntax #'[τ ...])])
                             (fully-unrestricted? t))]
           [_ #t])))

  (define (fail/type-convert src lang ty)
    (raise-syntax-error #f (format "cannot convert type ~a into ~a language"
                                   (type->str ty)
                                   (language-name lang))
                        src))

  ; convert-type : Symbol Type -> Type
  ;  converts a type into a more appropriate variant for the given language
  (define (convert-type lang type
                        #:src [fail-src #f]
                        #:fail [fail (λ (_) (fail/type-convert fail-src lang type))])
    (define converter
      (case lang
        [(L)
         (type-converter ([σ #:when (linear-type? #'σ) #'σ])
                         ([List =>  MList]
                          [×    =>  ⊗]
                          [→    =>  →]
                          [-o   =>  -o])
                         fail)]

        [(U)
         (type-converter ([τ #:when (fully-unrestricted? #'τ) #'τ])
                         ([MList =>  List]
                          [⊗    =>  ×]
                          [→     =>  →])
                         fail)]

        [else (error "invalid language" lang)]))

    ((current-type-eval) (converter type)))

  ; convert-syntax : Type Type Syntax -> Syntax
  ;  creates an expression that wraps the given syntax such that
  ;  it converts objects from the first type into the second type.
  ;  the resulting syntax will never evaluate the original syntax twice.
  ;  e.g.
  ;    (convert-stx #'(List Int) #'(MList Int) #'x)
  ;    ->
  ;    #'(foldr mcons '() x)
  (define (convert-syntax . args)
    (syntax-parse args
      [[τ σ src] #:when (type=? #'τ #'σ) #'src]

      ; convert tuples
      [[(~or (~⊗ τ ...) (~× τ ...)) (~or (~⊗ σ ...) (~× σ ...)) src]
       #:with [cad*r/tmp ...] (map (gen-cad*rs #'tmp)
                                   (range (stx-length #'[τ ...])))
       #:with [out ...] (stx-map convert-syntax
                                 #'[τ ...]
                                 #'[σ ...]
                                 #'[cad*r/tmp ...])
       #'(let- ([tmp src]) (#%app- list- out ...))]

      ; convert lists
      [[(~List τ) (~MList σ) src]
       #:with x+ (convert-syntax #'τ #'σ #'x)
       #'(#%app- foldr- (λ- (x l) (#%app- mcons- x+ l)) '() src)]

      [[(~MList τ) (~List σ) src]
       #:with x+ (convert-syntax #'τ #'σ #'x)
       #'(for/list- ([x (in-mlist src)]) x+)]

      ; convert functions
      [[(~or (~→ τ ... τ_out) (~-o τ ... τ_out))
        (~or (~→ σ ... σ_out) (~-o σ ... σ_out))
        src]
       #:with (x ...) (stx-map generate-temporary #'[τ ...])
       #:with (x+ ...) (stx-map convert-syntax #'[σ ...] #'[τ ...] #'[x ...])
       #:with out (convert-syntax #'τ_out #'σ_out #'(#%app- f x+ ...))
       #'(let- ([f src]) (λ- (x ...) out))]))

  )


; generate barrier crossing macros
(define-syntax define-barrier
  (syntax-parser
    [(_ form LANG)
     #'(define-typed-syntax LANG
         [(_ e) ≫
          #:when (eq? (syntax-local-context) 'expression)
          #:fail-when (eq? [current-language] 'LANG)
                      (format "already in ~a language"
                              (language-name 'LANG))
          #:mode current-language 'LANG ([⊢ e ≫ e- ⇒ τ])
          #:with σ (convert-type [current-language] #'τ #:src this-syntax)
          #:with e-- (convert-syntax #'τ #'σ #'e-)
          --------
          [⊢ e-- ⇒ σ]]

         ; expand toplevels using different syntax, bleh
         [(_ e ...+) ≫
          #:with e- (parameterize ([current-language 'LANG])
                      (local-expand #'(begin- e (... ...))
                                    'top-level
                                    '()))
          --------
          [≻ e-]])]

    [(_ LANG) #'(define-barrier LANG LANG)]))

(define-barrier L)
(define-barrier U)


; variable syntax
(define-typed-variable-syntax
  #:datum-literals (:)
  [(_ x- : τ) ≫
   #:when (eq? [current-language] 'U)
   #:fail-unless (fully-unrestricted? #'τ)
   (raise-syntax-error #f "cannot use linear variable from unrestricted language" #'x-)
   --------
   [⊢ x- ⇒ τ]]

  [(_ x- : σ) ≫
   #:when (eq? [current-language] 'L)
   --------
   [≻ (#%linear x- : σ)]])


; REPL prints expression types
; enter :lang=L or :lang=U to switch language in REPL
(define-typed-syntax #%top-interaction
  [(_ . d) ≫
   #:when (regexp-match #px":lang=." (~a (syntax-e #'d)))
   #:do [(current-language
          (string->symbol
           (second (regexp-match #px":lang=(.)" (~a (syntax-e #'d))))))
         (printf "; language: ~a\n" (language-name))]
   --------
   [≻ (#%app- void-)]]

  [(_ . e) ≫
   #:do [(printf "; language: ~a\n" (language-name))]
   [⊢ e ≫ e- ⇒ τ]
   --------
   [≻ (#%app- printf- '"~v : ~a\n" e- '#,(type->str #'τ))]])
