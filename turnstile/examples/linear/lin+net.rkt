#lang turnstile/lang
(require (prefix-in racket: (only-in racket thread))
         (only-in "lin+chan.rkt" → ⊗ InChan OutChan)
         "lin+net-utils.rkt")

(extends "lin+chan.rkt")
(extends "lin+var.rkt")

(reuse cons nil match-list MList MList0 #:from "lin+cons.rkt")
(reuse make-channel channel-get channel-put thread sleep InChan OutChan #:from "lin+chan.rkt")

(define-base-type TcpListener)

(provide (type-out TcpListener)
         (typed-out [[*tcp-listen : (→ Int TcpListener)] tcp-listen]
                    [[*tcp-accept : (→ TcpListener (⊗ TcpListener
                                                      (InChan String)  ; recieve packets
                                                      (OutChan String) ; send packets
                                                      (OutChan Unit)   ; close the connection
                                                      ))] tcp-accept]
                    [[tcp-close : (→ TcpListener Unit)] tcp-close])
         format)

(begin-for-syntax
  [current-linear? (or/c TcpListener? [current-linear?])])


(define-typed-syntax (format fstr:str arg ...) ≫
  [⊢ arg ≫ arg- ⇒ _] ...
  --------
  [⊢ (format- 'fstr arg- ...) ⇒ String])
