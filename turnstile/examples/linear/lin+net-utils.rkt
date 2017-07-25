#lang turnstile/lang
(require racket/tcp
         racket/port)
(provide (all-defined-out))

(define (*tcp-listen port)
  (tcp-listen port 4 #t))

(define (*tcp-accept listener)

  (define mgr (make-custodian))
  (define (kill) (custodian-shutdown-all mgr))

  (define-syntax-rule (with-mgr e ...)
    (with-handlers ([exn:fail:network? kill])
      e ...))

  (define-values (in out)
    (parameterize ([current-custodian mgr])
      (tcp-accept listener)))

  (define recv-chan (make-channel))
  (define send-chan (make-channel))
  (define kill-chan (make-channel))

  (define (recv-loop)
    (with-mgr
      (let ([s (sync (read-line-evt in 'any-one)
                     (port-closed-evt out))])
        (cond
          [(string? s)
           (channel-put recv-chan s)
           (recv-loop)]
          [else (kill)]))))

  (define (send-loop)
    (with-mgr
      (let ([s (sync send-chan
                     (port-closed-evt out))])
        (cond
          [(string? s)
           (write-string s out)
           (flush-output out)
           (send-loop)]
          [else (kill)]))))

  (define (kill-loop)
    (with-mgr
      (sync kill-chan (port-closed-evt out))
      (kill)))

  (thread recv-loop)
  (thread send-loop)
  (thread kill-loop)
  (list listener
        recv-chan
        send-chan
        kill-chan))
