#lang plait #:lazy

(define (f x y) x)

(define (ack m n)
  (cond
    [(zero? m) (+ n 1)]
    [(zero? n) (ack (- m 1) 1)]
    [else (ack (- m 1) (ack m (- n 1)))]))

;(f 1 (ack 4 4))

;(define (g x) (g x))

;(f 1 (g 2))

;(define (integer-from n)
;  (cons n (integer-from (+ n 1))))
;(define N (integer-from 0))
;N
;(first N)
;(second N)
;N
