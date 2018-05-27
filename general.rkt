#lang racket
(provide (all-defined-out))

(define (↓ m s)
  (let loop ((s s) (r (hash)))
    (if (set-empty? s)
        r
        (let ((key (set-first s)))
          (if (hash-has-key? m key)
              (loop (set-rest s) (hash-set r key (hash-ref m key)))
              (loop (set-rest s) r))))))

(define (hash-⊔ h1 h2 ⊔ ⊥)
  (for/fold ((h h1)) (((k2 v2) h2))
    (let ((v1 (hash-ref h1 k2 ⊥)))
      (hash-set h k2 (⊔ v1 v2)))))

(define (value->file value file)
  (let ((out (open-output-file file #:exists 'replace)))
    (write value out)
    (close-output-port out)))

(define (debug val . out)
  ;(printf "~a: ~a\n" (car out) (cdr out))
  val)