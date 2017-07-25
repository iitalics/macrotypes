#lang s-exp turnstile/examples/linear/lin+net

(define-type-alias Send (OutChan String))
(define-type-alias Recv (InChan String))

(define (send-all [chans : (MList Send)] [what : String]) (MList Send)
  (match-list chans
    [(cons ch rest @ l)
     (begin (channel-put ch what)
            (cons ch (send-all rest what) @ l))]
    [(nil) (nil)]))


(define-type-alias Broadcast
  (⊕ [joined String Send]
     [message String String]))

(define (broadcaster) (OutChan Broadcast)
  (let* ([(bc-in bc-out) (make-channel {Broadcast})])
    (letrec
        ([{handle : (→ Broadcast (MList Send) (MList Send))}
          (λ (b chans)
            (match b
              [(joined who c)
               (cons c (send-all chans (format "+ ~a has joined\n" who)))]

              [(message who what)
               (send-all chans (format "- ~a: ~a\n" who what))]))]

         [{poll : (→ (InChan Broadcast) (MList Send) Unit)}
          (λ (bc-in chans)
            (let* ([(bc-in+ x) (channel-get bc-in)]
                   [chans+ (handle x chans)])
              (poll bc-in+ chans+)))])

      (begin
       (thread (λ () (poll bc-in (nil))))
       bc-out))))

(define (client [recv : Recv]
                [send : Send]
                [broadcast : (OutChan Broadcast)]) Unit
  (letrec
      ([{ask-name : (→ Recv Unit)}
        (λ (recv)
          (begin
            (channel-put send "Enter your name: ")
            (let* ([(recv+ name) (channel-get recv)])
              (channel-put broadcast (var [joined name send]))
              (poll name recv+))))]

       [{poll : (→ String Recv Unit)}
        (λ (name recv)
          (let* ([(recv+ msg) (channel-get recv)])
            (channel-put broadcast (var [message name msg]))
            (poll name recv+)))])
    (thread (λ () (ask-name recv)))))


(define (server [port : Int]) Unit
  (let ([broadcast (broadcaster)])
    (letrec
        ([{poll : (→ TcpListener Unit)}
          (λ (lis)
            (let* ([(lis+ recv send kill) (tcp-accept lis)])
              (drop kill)
              (client recv send broadcast)
              (poll lis+)))])
      (poll (tcp-listen port)))))
