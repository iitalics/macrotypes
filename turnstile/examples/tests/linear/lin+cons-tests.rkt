#lang s-exp turnstile/examples/linear/lin+cons
(require turnstile/rackunit-typechecking)

(check-type
 (letrec ([{length : (→ (LList Int) Int)}
           (λ ! ([lst : (LList Int)])
              (match-list lst
                (cons _ xs @ l) ->
                  (begin (drop l)
                         (add1 (length xs)))
                nil -> 0))])
   (length (cons 9 (cons 8 (cons 7 (nil))))))
 : Int -> 3)


(check-type
 (letrec ([{rev-append : (→ (LList String) (LList String) (LList String))}
           (λ ! ([lst : (LList String)]
                 [acc : (LList String)])
              (match-list lst
                (cons x xs @ l) -> (rev-append xs (cons x acc @ l))
                nil -> acc))]

          [{rev : (→ (LList String) (LList String))}
           (λ ! ([lst : (LList String)])
              (rev-append lst (nil)))])

   (rev (cons "a" (cons "b" (cons "c" (nil))))))
 : (LList String)
 -> (cons "c" (cons "b" (cons "a" (nil)))))
