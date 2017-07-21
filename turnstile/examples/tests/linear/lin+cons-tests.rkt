#lang s-exp turnstile/examples/linear/lin+cons
(require turnstile/rackunit-typechecking)

(check-type
 (letrec ([{length : (→ (MList Int) Int)}
           (λ ! ([lst : (MList Int)])
              (match-list lst
                (cons _ xs @ l) ->
                  (begin (drop l)
                         (add1 (length xs)))
                nil -> 0))])
   (length (cons 9 (cons 8 (cons 7 (nil))))))
 : Int -> 3)


(check-type
 (letrec ([{rev-append : (→ (MList String) (MList String) (MList String))}
           (λ ! ([lst : (MList String)]
                 [acc : (MList String)])
              (match-list lst
                (cons x xs @ l) -> (rev-append xs (cons x acc @ l))
                nil -> acc))]

          [{rev : (→ (MList String) (MList String))}
           (λ ! ([lst : (MList String)])
              (rev-append lst (nil)))])

   (rev (cons "a" (cons "b" (cons "c" (nil))))))
 : (MList String)
 -> (cons "c" (cons "b" (cons "a" (nil)))))
