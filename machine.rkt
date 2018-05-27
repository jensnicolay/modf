#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(provide conc-eval)

(define ns (make-base-namespace))

;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
(struct clo (e ρ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<clo ~v>" (clo-e v))))
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
(struct ev (e ρ ι κ) #:transparent)
(struct ko (d ι κ) #:transparent)
(struct system (initial graph duration) #:transparent)


(define count!
  (let ((counter 0))
    (lambda ()
      (begin0
        counter
        (set! counter (add1 counter))))))

(define (index v x)
  (let ((i (vector-member x v)))
    (if i
        i
        (let ((i (add1 (vector-ref v 0))))
          (vector-set! v 0 i)
          (vector-set! v i x)
          i))))
(define stateis (make-vector 8000))
(define (state->statei q) (index stateis q))
(define ctxis (make-vector 2000))
(define (ctx->ctxi q) (index ctxis q))

;;;

(define (successors s g)
  (hash-ref g s (set)))

(define (explore e lat alloc kalloc)
    
  (define α (lattice-α lat))
  (define γ (lattice-γ lat))
  (define ⊥ (lattice-⊥ lat))
  (define ⊑ (lattice-⊑ lat))
  (define ⊔ (lattice-⊔ lat))
  (define true? (lattice-true? lat))
  (define false? (lattice-false? lat))
  (define α-eq? (lattice-eq? lat))

  (define S (set))
  (define σ (hash))
  (define C (hash))
  (define Ξ (hash))

  (define Compiled (set))
  ;(define M (hash))

  (define (store-lookup a)
    (hash-ref σ a))

  (define (store-alloc! a d)
    (if (hash-has-key? σ a) 
        (let* ((current (hash-ref σ a))
               (updated (⊔ current d)))
          (set! C (hash-set C a (add1 (hash-ref C a))))
          (unless (equal? current updated)
            (set! σ (hash-set σ a updated))
            (set! S (set)) 
            ))
        (begin
          (set! C (hash-set C a 1))
          (set! σ (hash-set σ a d))
          (set! S (set)) 
          )
        ))
          
  (define (store-update! a d)
    (let* ((current (hash-ref σ a))
           (c (hash-ref C a))
           (updated (if (= c 1)
                        d
                        (⊔ current d))))
      (unless (equal? current updated)
        (set! σ (hash-set σ a updated))
        (set! S (set)) 
        )))

  (define (alloc-literal! e)
    (if (pair? e)
        (let ((car-v (alloc-literal! (car e))))
          (let ((cdr-v (alloc-literal! (cdr e))))
            (let ((a (alloc e e)))
              (store-alloc! a (α (cons car-v cdr-v)))
              (α (addr a)))))
        (α e)))

  (define (atom-eval e ρ)
    (match e
      ((«lit» _ d)
       (α d))
      ((«id» _ x)
       (store-lookup (hash-ref ρ x)))
      ((«lam» _ _ _)
       (α (clo e ρ)))
      ((«quo» _ e)
       (α e))
      (_ (error "atom expected, got" e))))
  
  (define (step s)
    (match s
      ((ev («let» _ e-id e-init e-body) ρ ι κ)
       (set (ev e-init ρ (cons (letk e-id e-body ρ) ι) κ)))
      ((ev («letrec» _ e-id e-init e-body) ρ ι κ)
       (let* ((a (alloc e-id κ))
              (ρ* (hash-set ρ («id»-x e-id) a)))
         (set (ev e-init ρ* (cons (letreck a e-body ρ*) ι) κ))))
      ((ev («if» _ e-cond e-true e-false) ρ ι κ)
       (let ((d-cond (atom-eval e-cond ρ)))
         (set-union (if (true? d-cond) (set (ev e-true ρ ι κ)) (set))
                    (if (false? d-cond) (set (ev e-false ρ ι κ)) (set)))))
      ((ev («set!» _ («id» _ x) e) ρ ι κ)
       (let ((d (atom-eval e ρ)))
         (store-update! x d)
         (ko d ι κ)))
      ((ev (and e-app («app» _ e-rator e-rands)) ρ ι κ)
       (let ((d-rator (atom-eval e-rator ρ)))
         (for/fold ((S (set))) ((rator (in-set (γ d-rator))))
           (match rator
             ((clo («lam» _ xs e-body) ρ**)
              (let* ((d-rands (map (lambda (æ) (atom-eval æ ρ)) e-rands))
                     (κ* (kalloc rator d-rands)))
                (let bind-loop ((xs xs) (ρ* ρ**) (d-rands d-rands))
                  (if (null? xs)
                      (begin
                        (set! Ξ (hash-set Ξ κ* (set-add (hash-ref Ξ κ* (set)) (stack ι κ))))
                        (set-union S (set (ev e-body ρ* '() κ*))))
                      (let* ((e-param (car xs))
                             (x («id»-x e-param))
                             (a (alloc e-param κ*)))
                        (store-alloc! a (car d-rands))
                        (bind-loop (cdr xs) (hash-set ρ* x a) (cdr d-rands)))))))
             ((prim2 _ proc)
              (let* ((d-rands (map (lambda (æ) (atom-eval æ ρ)) e-rands))
                     (d-ret (apply proc d-rands)))
                (set-add S (ko d-ret ι κ))))
             ((prim _ proc)
              (let* ((d-rands (map (lambda (æ) (atom-eval æ ρ)) e-rands))
                     (D-ret (proc e-app κ d-rands)))
                (set-union S (for/set ((d-ret (in-set D-ret))) (ko d-ret ι κ)))))
             (_ S)))))
      ((ev («quo» _ e-quote) ρ ι κ)
       (let ((d (alloc-literal! e-quote)))
         (set (ko d ι κ))))
      ((ev e ρ ι κ)
       (let ((d (atom-eval e ρ)))
         (set (ko d ι κ))))
      ((ko d (cons (letk e-id e ρ) ι) κ)
       (let* ((a (alloc e-id κ))
              (ρ* (hash-set ρ («id»-x e-id) a)))
         (store-alloc! a d)
         (set (ev e ρ* ι κ))))
      ((ko d (cons (letreck a e ρ) ι) κ)
       (store-alloc! a d)
       (set (ev e ρ ι κ)))
      ((ko _ '() #f)
       (set))
      ((ko d '() κ)
       ;(let ((d* (⊔ (hash-ref M κ ⊥) d)))
        ; (set! M (hash-set M κ d*))
         (for/set ((st (in-set (hash-ref Ξ κ))))
           (ko d (stack-ι st) (stack-κ st))))
      ;)
      ))

  (define g (hash))
  
  (define (add-transitions! from tos)
    (set! g (hash-set g from (set-union (hash-ref g from (set)) tos))))

  (define (inject! e)

    (define ρ0 (hash))
    
    (define lat-glob (lattice-global lat))
    (define prim-glob (hash))
    
    (define (define-native-prim! name proc)
      (set! prim-glob (hash-set prim-glob name
                                (lambda ()
                                  (store-alloc! name (α (prim name proc)))))))
                                                
    (define (define-compile-prim! name e)
      (set! prim-glob (hash-set prim-glob name
                                (lambda ()
                                  (let ((e-lam (compile e)))
                                    (define-prims! (free e-lam))
                                    (let ((clo-prim (atom-eval e-lam ρ0)))
                                      (set! Compiled (set-add Compiled clo-prim))
                                      (store-alloc! name clo-prim)))))))                                            
                              
    (define-native-prim! "cons"
      (lambda (e-app κ d-rands)
        (let ((a (alloc e-app κ)))
          (store-alloc! a (α (cons (car d-rands) (cadr d-rands))))
          (set (α (addr a))))))

    (define-native-prim! "list"
      (lambda (e-app κ d-rands)
        (let ((e-rands («app»-aes e-app)))
          (set (list-alloc-helper! d-rands e-rands κ)))))

    (define (list-alloc-helper! d-rands e-rands κ)
      (if (null? d-rands)
          (α '())
          (let ((d-cdr (list-alloc-helper! (cdr d-rands) (cdr e-rands) κ)))
            (let ((a (alloc (car e-rands) κ)))
              (store-alloc! a (α (cons (car d-rands) d-cdr)))
              (α (addr a))))))

    (define-native-prim! "car"
      (lambda (_ __ d-rands)
        (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
               (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
                 (⊔ d (car w)))))))

    (define-native-prim! "set-car!"
      (lambda (_ __ d-rands)
        (let ((d (cadr d-rands)))
          (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
            (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
              (store-update! (addr-a a) (α (cons d (cdr w))))))
          (set (α 'undefined)))))

    (define-native-prim! "cdr"
      (lambda (_ __ d-rands)
        (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
               (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
                 (⊔ d (cdr w)))))))
    
    (define-native-prim! "set-cdr!"
      (lambda (_ __ d-rands)
        (let ((d (cadr d-rands)))
          (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
            (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
              (store-update! (addr-a a) (α (cons (car w) d)))))
          (set (α 'undefined)))))

    (define-native-prim! "pair?"
      (lambda (_ __ d-rands)
        (let ((d (for/fold ((d ⊥)) ((w (in-set (γ (car d-rands)))))
                   (match w
                     ((addr a)
                      (for/fold ((d d)) ((ww (in-set (γ (store-lookup a)))))
                        (⊔ d (α (pair? ww)))))
                     (_
                      (⊔ d (α #f)))))))
          (set d))))
    
    (define-native-prim! "eq?"
      (lambda (_ __ d-rands)
        (set (for*/fold ((d ⊥)) ((w1 (γ (car d-rands))) (w2 (γ (cadr d-rands))))
               (⊔ d (match* (w1 w2)
                      (((addr a) (addr a))
                       (α #t))
                      (((addr _) (addr _))
                       (α #f))
                      ((_ _)
                       (α-eq? w1 w2))))))))

    (define (equal?-helper d1 d2)
      (for*/fold ((d ⊥)) ((w1 (γ d1)) (w2 (γ d2)))
        (⊔ d (match* (w1 w2)
               (((addr a) (addr a))
                (α #t))
               (((addr a1) (addr a2))
                (let ((d1 (store-lookup a1))
                      (d2 (store-lookup a2)))
                  (equal?-helper d1 d2)))
               (((cons d1 d2) (cons d3 d4))
                (let ((d* (equal?-helper d1 d3)))
                  (if (true? d*)
                      (if (false? d*)
                          d*
                          (equal?-helper d2 d4))
                      d*)))
               ((_ _)
                (α-eq? w1 w2))))))
  
    (define-native-prim! "equal?"
      (lambda (_ __ d-rands)
        (set (equal?-helper (car d-rands) (cadr d-rands)))))

    (define-native-prim! "error"
      (lambda _ (set)))

    (define-native-prim! "display"
      (lambda (_ __ d-rands)
        (printf "~v\n" d-rands)
        (set 'undefined)))

    (define-compile-prim! "cadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (car x))))

    (define-compile-prim! "caddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (car y)))))

    (define-compile-prim! "member"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (equal? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (member v d)))))))))

    (define (define-prims! W-free)
      (unless (set-empty? W-free)
        (let ((x (set-first W-free)))
          (unless (hash-has-key? ρ0 x)
            (set! ρ0 (hash-set ρ0 x x))
            (let ((action (hash-ref prim-glob x #f)))
              (or (and action (action)) 
                  (match (assoc x lat-glob)
                    ((cons _ pr2)
                     (set! ρ0 (hash-set ρ0 x x))
                     (store-alloc! x pr2))
                    (#f (error "unbound variable" x))))))
          (define-prims! (set-rest W-free)))))

    (define-prims! (free e))
    (ev e ρ0 '() #f))
  
  (define (explore! W)
    (unless (set-empty? W)
      (let ((s (set-first W)))
        (if (set-member? S s)
            (explore! (set-rest W))
            (let* ((succs (step s))
                   (W* (set-union (set-rest W) succs))
                   (S* (set-add S s)))
              ;(printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei)))
              (add-transitions! s succs)
              (set! S S*)
              (explore! W*))))))

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


  (define (compiled-state? s)
    (match s
      ((ev _ _ _ (cons rator _)) (set-member? Compiled rator))
      ((ko _ _ (cons rator _)) (set-member? Compiled rator))
      (_ #f)))

  (let ((t-start (current-milliseconds)))
    (let ((s0 (inject! e)))
      (explore! (set s0))
      (let ((t-end (current-milliseconds)))
        (let ((t-prune-start (current-milliseconds)))
          (let ((g* (prune s0 g compiled-state?))) ; TODO: prune Ξ
            (let ((t-prune-end (current-milliseconds)))
              (let ((prune-duration (- t-prune-end t-prune-start)))
                (let ((duration (- t-prune-end t-start)))
                  (printf "exploration ~v ms; pruning ~v ms\n" (- t-end t-start) (- t-prune-end t-prune-start))
                  (system s0 g* duration))))))))))

(define (end-states g)
  (for/set (((from tos) (in-hash g)) #:when (set-empty? tos))
    from))

(define (evaluate e lat alloc kalloc)
  (let* ((sys (explore e lat alloc kalloc))
         (g (system-graph sys))
         (s0 (system-initial sys))
         (S-end (end-states g)))
    (printf "~v states in ~v ms\n" (set-count (set-union (hash-keys g) (hash-values g))) (system-duration sys))
    (generate-dot s0 g "grapho")
    (for/fold ((d (lattice-⊥ lat))) ((s (in-set S-end)) #:when (ko? s))
      ((lattice-⊔ lat) d (ko-d s)))))
    
(define (conc-alloc e κ)
  (count!))

(define (conc-kalloc rator rands)
  (cons rator (count!)))
                     
(define (conc-eval e)
  (evaluate e conc-lattice conc-alloc conc-kalloc))

(define (type-alloc e κ)
  e)

(define (type-kalloc rator rands)
  (cons rator rands))

(define (type-eval e)
  (evaluate e type-lattice type-alloc type-kalloc))

(define (state-repr s)
  (match s
    ((ev e _ _ κ) (format "(ev ~a ~v)" (~a e #:max-width 40) (ctx->ctxi κ)))
    ((ko d _ κ) (format "(ko ~a ~v)" (~a d #:max-width 40) (ctx->ctxi κ)))))

(define (generate-dot s0 g name)
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
    (fprintf dotf "digraph G {\n")
    (let loop ((S (set)) (W (set s0)))
      (if (set-empty? W)
          (begin
            (fprintf dotf "}")
            (close-output-port dotf))
          (let ((s (set-first W)))
            (if (set-member? S s)
                (loop S (set-rest W))
                (let ((S* (set-add S s))
                      (S-succ (hash-ref g s (set)))
                      (si (state->statei s)))
                  (fprintf dotf "~a [label=\"~a | ~a\"];\n" si si (state-repr s))
                  (for ((s* S-succ))
                    (let ((si* (state->statei s*)))
                      (fprintf dotf "~a -> ~a;\n" si si*)))
                  (loop S* (set-union (set-rest W) S-succ)))))))))

;;; TESTS

(type-eval
 (compile

  ;'(let ((l '(list 1 2 3)))
  ;   (pair? l))

  ;'(let ((v '(1 2)))
  ;   (let ((w '(2 2)))
  ;     (equal? v w)))

 ;'(let ((p '(1 2 3 4)))
 ;   (member 8 p))
     
;'(letrec ((f (lambda (x) (* x x)))) (f 4))
  
 ; '(let ((p (cons 1 #t)))
 ;    (let ((z (set-car! p 123)))
 ;      (car p)))
  
 (file->value "test/deriv.scm")

  )) 


;(conc-eval
; (compile '(let ((x 1))
;             (let ((y (+ x 1)))
;               (let ((c (= y 2)))
;                 (let ((z (if c (set! x 2) (set! x 3))))
;                   (+ x y)))))))
