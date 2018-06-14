#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require (prefix-in conc: "conc-machine.rkt"))
(require (prefix-in aam: "machine.rkt"))
(require (prefix-in modf: "modf-qj.rkt"))

(define stateis (make-vector 8000))
(define (state->statei q) (index stateis q))
(define ctxis (make-vector 2000))
(define (ctx->ctxi q) (index ctxis q))


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
                     
(define (conc-eval e)
  (evaluate e conc:explore conc-lattice conc-alloc conc-kalloc))



(define (type-alloc e κ)
  e)

(define (type-kalloc rator rands)
  (cons rator rands))

(define (modf-kalloc rator rands ρ*)
  (cons («lam»-e0 (clo-e rator)) ρ*))

(define (type-eval e)
  (evaluate e aam:explore type-lattice type-alloc modf-kalloc)) ; !!! MODF

(define (state-repr s)
  (match s
    ((ev e _ _ κ) (format "(ev ~a ~v)" (~a e #:max-width 40) (ctx->ctxi κ)))
    ((ko d _ κ) (format "(ko ~a ~v)" (~a d #:max-width 40) (ctx->ctxi κ)))))

(define (result-state? s κ0)
  (match s
    ((ko d '() (== κ0))     
     #t)
    (_
     #f)))

(define (result-states g s0)
  (let loop ((S (set)) (W (set s0)) (S-res (set)))
    (if (set-empty? W)
        S-res
        (let ((s (set-first W)))
          ;(printf "insp ~v ~v\n" (state->statei s) (set-map (hash-ref g s (set)) state->statei))
          (if (set-member? S s)
              (loop S (set-rest W) S-res)
              (let ((S* (set-add S s))
                    (S-succ (hash-ref g s (set))))
                (if (result-state? s)
                    (loop S* (set-union (set-rest W) S-succ) (set-add S-res s))
                    (loop S* (set-union (set-rest W) S-succ) S-res))))))))


(define (evaluate e explore lat alloc kalloc)
  (let* ((sys (explore e lat alloc kalloc))
         (g (system-graph sys))
         (s0 (system-initial sys))
         (κ0 (ev-κ s0))
         (states (apply set-union (cons (list->set (hash-keys g)) (hash-values g)))))
    (printf "~v states in ~v ms\n" (set-count states) (system-duration sys))
    (generate-dot s0 g "grapho")
    (for/fold ((d (lattice-⊥ lat))) ((s (in-set states)) #:when (result-state? s κ0))
      ((lattice-⊔ lat) d (ko-d s)))))

(define (generate-dot s0 g name)
  ;    (match from ; TODO investigate non-result end states
;      ((ev e _ ι κ)
;       'ok)
;      ((ko d ι κ)
;       (printf "??? ~a\n~a\n\n" ι κ)))
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
    (fprintf dotf "digraph G {\n")
    (for (((s S-succ) (in-hash g)))
      (let ((si (state->statei s)))
        ;(printf "output ~a\n" si)
        (fprintf dotf "~a [label=\"~a | ~a\"];\n" si si (state-repr s))
        (for ((s* S-succ))
          (let ((si* (state->statei s*)))
            (fprintf dotf "~a -> ~a;\n" si si*)))))
    (fprintf dotf "}")
    (close-output-port dotf)))
;dot -Tpdf grapho.dot -o grapho.pdf

(conc-eval
 (compile
  (file->value "test/5.14.3.scm")
  ))