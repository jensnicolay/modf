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

(define (index v x)
  (let ((i (vector-member x v)))
    (if i
        i
        (let ((i (add1 (vector-ref v 0))))
          (vector-set! v 0 i)
          (vector-set! v i x)
          i))))


(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
(struct clo (e ρ) #:transparent)
  ;#:property prop:custom-write (lambda (v p w?)
  ;                               (fprintf p "<clo ~v>" (clo-e v))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct compiled (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (compiled-name s1) (compiled-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (compiled-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (compiled-name s))))))
(struct addr (a) #:transparent)
(struct stack (ι κ) #:transparent)
;(struct ctx (e ρ) #:transparent)
(struct ev (e ρ ι κ) #:transparent)
(struct ko (d ι κ) #:transparent)
(struct system (initial graph σ duration) #:transparent)

