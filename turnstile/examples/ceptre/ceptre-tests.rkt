#lang s-exp turnstile/examples/ceptre/ceptre
;; "blocks world" example from:
;;   https://github.com/chrisamaphone/interactive-lp/blob/master/examples/blocks-world.cep

(define Block : Type)
(define (on Block Block) : Pred)
(define (on-table Block) : Pred)
(define (clear Block) : Pred)
(define (arm-holding Block) : Pred)
(define arm-free : Pred)

(define a : Block)
(define b : Block)
(define c : Block)

(define-stage blocks

  (pickup-from-block (* (on 'x 'y) (clear 'x) arm-free)
                     -o
                     (* (clear 'y) (arm-holding 'x)))

  (pickup-from-table (* (on-table 'x) (clear 'x) arm-free)
                     -o
                     (* (arm-holding 'x)))

  (put-on-block (* (arm-holding 'x) (clear 'y))
                -o
                (* (on 'x 'y) (clear 'x) arm-free))

  (put-on-table (arm-holding 'x)
                -o
                (* (on-table 'x) (clear 'x) arm-free))

  )

#;
(interactive blocks
             { (on-table a)
               (on-table b)
               (on c a)
               (clear c)
               (clear b)
               arm-free })



(define Nat : Type)
(define Z : Nat)
(define (S Nat) : Nat)

(define (PLUS Nat Nat Nat) : Pred)

(define-stage arith
  (dup 'a -o (* 'a 'a))
  (splus (PLUS 'x 'y 'x+y) -o (PLUS (S 'x) 'y (S 'x+y)))
  )
