#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require (prefix-in conc: "conc-machine.rkt"))
(require (prefix-in aam: "aac.rkt"))
(require (prefix-in modf: "modf.rkt"))

(define count!
  (let ((counter -1))
    (lambda ()
      (begin
        (set! counter (add1 counter))
        counter))))

(define (conc-alloc e κ)
  (cons (count!) (type-alloc e κ)))

(define (conc-kalloc rator rands ρ*)
  (cons rator (count!)))
                     
;(define (conc-eval e)
;  (evaluate e conc-lattice conc-alloc conc-kalloc))

(define α (lattice-α type-lattice))
(define ⊑ (lattice-⊑ type-lattice))
;(define ⊔ (lattice-⊔ type-lattice))


(define (type-alloc e κ)
  e)

(define (type-kalloc rator rands)
  (cons rator rands))

(define (modf-kalloc rator rands ρ*)
  (cons («lam»-e0 (clo-e rator)) ρ*))

;(define (type-eval e)
;  (evaluate e type-lattice type-alloc modf-kalloc)) ; !!! MODF

;(define (state-repr s)
;  (match s
;    ((ev e _ _ κ) (format "(ev ~a ~v)" (~a e #:max-width 40) (ctx->ctxi κ)))
;    ((ko d _ κ) (format "(ko ~a ~v)" (~a d #:max-width 40) (ctx->ctxi κ)))))

(define (filter-contexts σ)
  (for/hash (((a d) (in-hash σ)) #:unless (and (pair? a) (struct? (car a))))
    ;(when (and (pair? a) (struct? (car a)))
    ;  (printf "filter ~a\n" a))
    (values a d)))

(define (result-state? s κ0)
  (match s
    ((ko d '() (== κ0))     
     #t)
    (_
     #f)))

(define (abst x)
  (if (addr? x)
      (type-α (addr (cdr (addr-a x))))
      (type-α x)))

(define (print-benchmark-row name results)
  (define node-count (hash-ref results 'node-count))
  (define lam-count (hash-ref results 'lam-count))
  (define set!-count (hash-ref results 'set!-count))
  (define set-car!-count (hash-ref results 'set-car!-count))
  (define set-cdr!-count (hash-ref results 'set-cdr!-count))
  (define vector-set!-count (hash-ref results 'vector-set!-count))
  (define cons-count (hash-ref results 'cons-count))
  (define make-vector-count (hash-ref results 'make-vector-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~a node-count #:min-width 6)
          (~a lam-count #:min-width 3)
          (~a set!-count #:min-width 3)
          (~a cons-count #:min-width 3)
          (~a set-car!-count #:min-width 3)
          (~a set-cdr!-count #:min-width 3)
          (~a make-vector-count #:min-width 3)
          (~a vector-set!-count #:min-width 3)
          ))

; (define (print-benchmarks)
;   (printf "benchmarks\n")
;   (for ((r test-result))
;        (let* ((benchmark-name (car r))
;               (results (cadr r)))
;          (print-benchmark-row benchmark-name results))))

;(define (store-⊑ σ1 σ2)
;  (if (equal? σ1 σ2)
;      #t
;      (if #f;(< (hash-count σ2) (hash-count σ1))
;          #f
;          (for/and (((k v) σ1))
;            (if (hash-has-key? σ2 k)
;                (if (⊑ v (hash-ref σ2 k))
;                    'ok
;                    (printf "key ~a \n\tvalue?\n1 ~a\n2 ~a\n" k v (hash-ref σ2 k)))
;                (printf "key? ~a\n" k))
;            (and (hash-has-key? σ2 k)
;                 (real-⊑ v (hash-ref σ2 k)))))))

(define (benchmark names)
  (for ((name (in-list names)))
    (printf "~a\n" name)
    (let* ((e (compile (file->value (string-append "test/" name ".scm"))))
           ;(conc (perform-benchmark e name "conc" conc:explore conc-lattice conc-alloc conc-kalloc))
           (aam (perform-benchmark e name "aam" aam:explore type-lattice type-alloc modf-kalloc))
           (modf (perform-benchmark e name "modf" modf:explore type-lattice type-alloc modf-kalloc)))

;      (printf "subsumption d-result\n")
;      (let ((d-result-conc (abst (hash-ref conc 'd-result)))
;            (d-result-aam (hash-ref aam 'd-result))
;            (d-result-modf (hash-ref modf 'd-result)))
;        (unless (⊑ d-result-conc d-result-aam)
;          (printf "aam does not subsume conc: conc ~a aam ~a\n" d-result-conc d-result-aam))
;        (unless (⊑ d-result-conc d-result-modf)
;          (printf "modf does not subsume conc: conc ~a modf ~a\n" d-result-conc d-result-modf)))

;      (printf "subsumption σ\n")
;      (let ((σ-conc (hash-ref conc 'σ))
;            (σ-aam (hash-ref aam 'σ))
;            (σ-modf (hash-ref modf 'σ)))
;        ;(printf "\n~a\n\n~a\n\n~a\n"  σ-conc σ-aam σ-modf)
;        (unless (store-⊑ σ-conc σ-aam)
;          (printf "aam does not subsume conc\n"))
;        (unless (store-⊑ σ-conc σ-modf)
;          (printf "modf does not subsume conc\n")))

      
      
    (printf "\n"))))
       
(define (perform-benchmark e name machine-name explore lattice alloc kalloc)
  (define γ (lattice-γ lattice))
  (define ⊥ (lattice-⊥ lattice))
  (define ⊔ (lattice-⊔ lattice))

  (let* ((sys (explore e lattice alloc kalloc))
         (g (system-graph sys))
         (s0 (system-initial sys))
         (κ0 (ev-κ s0))
         (states (apply set-union (cons (list->set (hash-keys g)) (hash-values g))))
         (state-count (set-count states))
         (σ (filter-contexts (system-σ sys)))
         (store-key-size (hash-count σ))
         (store-value-size (for/sum ((d (in-set (hash-values σ))))
                             (set-count (γ d))))
         (store-mono-size (for/sum (((a d) (in-hash σ)))
                             (if (and (struct? a) (= 1 (set-count (γ d))))
                                 1
                                 0)))
         (d-result (for/fold ((d ⊥)) ((s (in-set states)) #:when (result-state? s κ0))
                     (⊔ d (ko-d s)))))
    (printf "~a ~a ~a output ~a keys ~a values ~a mono ~a\n" (~a machine-name #:min-width 8) (~a state-count #:min-width 12)
            (~a (system-duration sys) #:min-width 12) (~a (set-count (γ d-result)) #:min-width 4)
            (~a store-key-size #:min-width 6) (~a store-value-size #:min-width 8) (~a store-mono-size #:min-width 6))
    (hash 'σ σ 'd-result d-result)))

(benchmark (list
            "fib" ;  warmup
            "collatz" ; warmup
            "browse"
            "churchnums"
            "classtree"
            "dderiv"
            "deriv"
            "destruc"
            "fannkuch"
            "graphs"
            ;"grid"
            "matrix"
            "mazefun"
            "mceval"
            "partialsums"
            "primtest"
            "regex"
            "scm2java"
            "spectralnorm"
            "supermerge"
            "treeadd"
            "triangl"
            "boyer"
            ))
