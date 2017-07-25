#lang s-exp turnstile/examples/linear/lin+net

(define-type-alias Send (OutChan String))
(define-type-alias Recv (InChan String))

;; send a string to all of the channels in a list
(define (send-all [chans : (MList Send)] [what : String]) (MList Send)
  (match-list chans
    [(cons ch rest @ l)
     (begin (channel-put ch what)
            (cons ch (send-all rest what) @ l))]
    [(nil) (nil)]))


(define-type-alias Broadcast
  (⊕ [joined String Send]
     [message String String]))

;; spawns a broadcaster thread which waits for messages of the above form.
;;   [joined who send-chan] adds 'send-chan' to the list of clients (and notifies others)
;;   [message who what] sends a message to all of the clients
(define (broadcaster) (OutChan Broadcast)
  (let* ([(bc-in bc-out) (make-channel {Broadcast})])
    (letrec
        ([{handle : (→ Broadcast (MList Send) (MList Send))}
          ;; handle a broadcast object
          (λ (b chans)
            (match b
              [(joined who c)
               (cons c (send-all chans (format "+ ~a has joined\n" who)))]

              [(message who what)
               (send-all chans (format "- ~a: ~a\n" who what))]))]

         [{poll : (→ (InChan Broadcast) (MList Send) Unit)}
          ;; wait for new broadcasts and repeat
          (λ (bc-in chans)
            (let* ([(bc-in+ x) (channel-get bc-in)]
                   [chans+ (handle x chans)])
              (poll bc-in+ chans+)))])

      (begin
       (thread (λ () (poll bc-in (nil))))
       bc-out))))


;; spawns a client thread which waits for client messages and sends them
;; to the broadcast thread.
(define (client [recv : Recv] [send : Send]
                [broadcast : (OutChan Broadcast)]) Unit
  (letrec
      ([{ask-name : (→ Recv Unit)}
        ;; ask for the user's name then start polling for individual messages
        (λ (recv)
          (begin
            (channel-put send "Enter your name: ")
            (let* ([(recv+ name) (channel-get recv)])
              (channel-put broadcast (var [joined name send]))
              (poll name recv+))))]

       [{poll : (→ String Recv Unit)}
        ;; wait for messages and then broadcast them
        (λ (name recv)
          (let* ([(recv+ msg) (channel-get recv)])
            (channel-put broadcast (var [message name msg]))
            (poll name recv+)))])
    (thread (λ () (ask-name recv)))))


(define (server [port : Int]) Unit
  (let ([broadcast (broadcaster)])
    (letrec
        ([{poll : (→ TcpListener Unit)}
          ;; wait for client connections
          (λ (lis)
            (let* ([(lis+ recv send kill) (tcp-accept lis)])
              (drop kill)
              (client recv send broadcast)
              (poll lis+)))])
      (poll (tcp-listen port)))))
