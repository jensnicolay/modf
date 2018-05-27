#lang racket

  (define (prune s0 g pred?)
  (let loop ((S (set)) (W (set (list s0 #f #f))) (R (hash)) (g* (hash)))
    (if (set-empty? W)
        g*
        (let ((el (set-first W)))
          (match el
            ((list s s-prev #f)
             ;(printf "1: el ~v ~v ~v ~v\n\n" (state-repr s) (state->statei s) (and s-prev (state-repr s-prev)) (and s-prev (state->statei s-prev)))
             (if (hash-has-key? R s)
                 (loop S (set-rest W) R (hash-set g* s-prev (set-union (hash-ref g* s-prev (set)) (hash-ref R s))))
                 (if (set-member? S s)
                     (loop S (set-rest W) g*)
                     (if (pred? s)
                         (loop (set-add S s)
                               (for/fold ((W (set-rest W))) ((s* (hash-ref g s)))
                                 (set-add W (list s* s-prev (set s))))
                               R
                               g*)
                         (loop (set-add S s)
                               (for/fold ((W (set-rest W))) ((s* (hash-ref g s)))
                                     (set-add W (list s* s #f)))
                               R
                               (if s-prev
                                   (hash-set g* s-prev (set-add (hash-ref g* s-prev (set)) s))
                                   g*))))))
            ((list s s-prev G)
             ;(printf "2: el ~v ~v ~v ~v COUNT ~v\n\n" (state-repr s) (state->statei s) (state-repr s-prev) (state->statei s-prev) (set-count G))
             (if (set-member? S s)
                 (loop S (set-rest W) g*)
                 (if (pred? s)
                     (loop (set-add S s)
                           (for/fold ((W (set-rest W))) ((s* (hash-ref g s)))
                             (set-add W (list s* s-prev (set-add G s))))
                           R
                           g*)
                     (loop (set-add S s)
                             (for/fold ((W (set-rest W))) ((s* (hash-ref g s)))
                               (set-add W (list s* s #f)))
                             (hash-set R s (set-union (hash-ref R s (set)) G))
                             (hash-set g* s-prev (set-add (hash-ref g* s-prev (set)) s)))))))))))








(define (prune s0 g pred?)

    (define (remove-vertex g s)
      (let ((S-succ (successors s g))
            (S-pred (for/set (((s* S*) (in-hash g)) #:when (set-member? S* s))
                      s*)))
        (for/fold ((g g)) ((s-pred (in-set S-pred)))
          (hash-set g s-pred (set-union (set-remove (hash-ref g s-pred) s) S-succ)))))
    
    (let loop ((S (set)) (W (set s0)) (g g))
      (if (set-empty? W)
          g
          (let ((s (set-first W)))
            (if (set-member? S s)
                (loop S (set-rest W) g)
                (if (pred? s)
                    (let ((g* (remove-vertex g s)))
                      (loop (set-add S s) (set-union (set-rest W) (hash-ref g* s (set))) g*))
                    (loop (set-add S s) (set-union (set-rest W) (hash-ref g s (set))) g)))))))
