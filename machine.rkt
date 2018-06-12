#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(random-seed 111)

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
;(define ctxis (make-vector 2000))
;(define (ctx->ctxi q) (index ctxis q))

;;;

(define (successors s g)
  (hash-ref g s (set)))

;(printf "NO clear of visited for new address\n")

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
  ;(define C (hash))
  (define Ξ (hash))

  (define Compiled (set))

  (define (store-lookup a)
    (hash-ref σ a))

  ;(define store-size 0)
  ;(define prev-store-size 0)
  ;(define (set-store-size! new)
  ;  (unless (= new prev-store-size)
  ;    (set! prev-store-size store-size)
  ;    (set! store-size new)
  ;    (printf "store-size ~v\n" new)))

  (define (store-alloc! a d)
    (if (hash-has-key? σ a) 
        (let* ((current (hash-ref σ a))
               (updated (⊔ current d)))
          ;(set! C (hash-set C a (add1 (hash-ref C a))))
          (unless (equal? current updated)
            (set! σ (hash-set σ a updated))
   ;         (set-store-size! (+ (- store-size (set-count current)) (set-count updated)))
            ;(printf "alloc ~a -> ~a\n" (set-count current) (set-count updated))
            (set! S (set))         
            ))
        (begin
          ;(set! C (hash-set C a 1))
          (set! σ (hash-set σ a d))
    ;      (set-store-size! (+ store-size (set-count d)))
          ;(printf "address ~a\n" (set-count (hash-keys σ)))
          (set! S (set))
          )
        ))
          
  (define (store-update! a d)
    (let* ((current (hash-ref σ a))
           ;(c (hash-ref C a))
           (updated (if #f;(= c 1)
                        d
                        (⊔ current d))))
      (unless (equal? current updated)
        (set! σ (hash-set σ a updated))
     ;   (set-store-size! (+ (- store-size (set-count current)) (set-count updated)))
        ;(printf "update ~a -> ~a\n" (set-count current) (set-count updated))
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
      ((ev («set!» _ («id» _ x) e0) ρ ι κ)
       (let ((a (hash-ref ρ x))
             (d (atom-eval e0 ρ)))
         (store-update! a d)
         (set (ko d ι κ))))
      ((ev (and e-app («app» _ e-rator e-rands)) ρ ι κ)
       (let ((d-rator (atom-eval e-rator ρ))
             (d-rands (map (lambda (æ) (atom-eval æ ρ)) e-rands)))
         (for/fold ((S (set))) ((rator (in-set (γ d-rator))))
           (match rator
             ((clo («lam» _ xs e-body) ρ**)
              (let ((d-rands (map (lambda (æ) (atom-eval æ ρ)) e-rands)))
                (let bind-loop ((xs xs) (ρ* ρ**) (d-rands d-rands))
                  (if (null? xs)
                      (let ((κ* (kalloc rator d-rands ρ*)))
                        (set! Ξ (hash-set Ξ κ* (set-add (hash-ref Ξ κ* (set)) (stack ι κ))))
                        (set-union S (set (ev e-body ρ* '() κ*))))
                      (if (null? d-rands)
                          S
                          (let* ((e-param (car xs))
                                 (x («id»-x e-param))
                                 (a (alloc e-param 'TODO)))
                            (store-alloc! a (car d-rands))
                            (bind-loop (cdr xs) (hash-set ρ* x a) (cdr d-rands))))))))
             ((prim2 _ proc)
              (let ((d-ret (apply proc d-rands)))
                (set-add S (ko d-ret ι κ))))
             ((prim _ proc)
              (let ((D-ret (proc e-app κ d-rands)))
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

    ;(define-native-prim! "apply"
    ;  (lambda (e-app κ d-rands)
    ;    (

    
    (define-native-prim! "cons"
      (lambda (e-app κ d-rands)
        (let ((a (alloc e-app κ)))
          (store-alloc! a (α (cons (car d-rands) (cadr d-rands))))
          (set (α (addr a))))))

    (define-native-prim! "list"
      (lambda (e-app κ d-rands)
        (let ((e-rands («app»-es e-app)))
          (set (list-alloc-helper! d-rands e-rands κ)))))

    (define (list-alloc-helper! d-rands e-rands κ)
      (if (null? d-rands)
          (α '())
          (let ((d-cdr (list-alloc-helper! (cdr d-rands) (cdr e-rands) κ)))
            (let ((a (alloc (car e-rands) κ)))
              (store-alloc! a (α (cons (car d-rands) d-cdr)))
              (α (addr a))))))    

    (define-native-prim! "car"
      (lambda (_ κ d-rands)
        (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
               (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
                 (⊔ d (car w)))))))

    (define-native-prim! "set-car!"
      (lambda (_ κ d-rands)
        (let ((d (cadr d-rands)))
          (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
            (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
              (store-update! (addr-a a) (α (cons d (cdr w))))))
          (set (α 'undefined)))))

    (define-native-prim! "cdr"
      (lambda (_ κ d-rands)
        (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
               (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
                 (⊔ d (cdr w)))))))
    
    (define-native-prim! "set-cdr!"
      (lambda (_ κ d-rands)
        (let ((d (cadr d-rands)))
          (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
            (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
              (store-update! (addr-a a) (α (cons (car w) d)))))
          (set (α 'undefined)))))

    (define-native-prim! "pair?"
      (lambda (_ κ d-rands)
        (let ((d (for/fold ((d ⊥)) ((w (in-set (γ (car d-rands)))))
                   (match w
                     ((addr a)
                      (for/fold ((d d)) ((ww (in-set (γ (store-lookup a)))))
                        (⊔ d (α (pair? ww)))))
                     (_
                      (⊔ d (α #f)))))))
          (set d))))

    (define-native-prim! "make-vector"
      (lambda (_ κ d-rands)
        (let* ((a (alloc e κ))
               (num (car d-rands))
               (lt-proc (lambda (x y)
                          (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "<" lat-glob)))))
                            (⊔ result ((prim2-proc prim2) x y))))) ; TODO check whether we can use conc +1 and then α
               (add-proc (lambda (x y)
                           (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "+" lat-glob)))))
                             (⊔ result ((prim2-proc prim2) x y)))))
               (init (cadr d-rands))
               (h (hash)))
          (let loop ((h h) (i (α 0)))
            (if (and (true? (lt-proc i num)) (not (hash-has-key? h i)))
                (loop (hash-set h i init) (add-proc i (α 1)))
                (let ((v (α h)))
                  (store-alloc! a v)
                  (set (α (addr a)))))))))

    (define-native-prim! "vector"
      (lambda (_ κ d-rands)
        (let* ((a (alloc e 'TODO))
               (num (length d-rands))
               (h (hash)))
          (let loop ((h h) (d-rands d-rands) (i 0))
            (if (null? d-rands)
                (let ((v (α h)))
                  (store-alloc! a v)
                  (set (α (addr a))))
                (loop (hash-set h (α i) (car d-rands)) (cdr d-rands) (add1 i)))))))

    (define-native-prim! "vector-ref"
      (lambda (_ κ d-rands)
        (let ((index (cadr d-rands)))
          (let ((v (for/fold ((v ⊥)) ((w (γ (car d-rands))))
                     (match w
                       ((addr a)
                        (for/fold ((v v)) ((ww (γ (store-lookup a))))
                          (if (hash? ww)
                              (for/fold ((v v)) (((key val) ww))
                                (if (or (⊑ index key) (⊑ key index) )
                                    (⊔ v val)
                                    v))
                              v)))
                       (_ v )))))
            (set v)))))

    (define-native-prim! "vector-set!"
      (lambda (_ κ d-rands)
        (let ((v1 (car d-rands))
              (v2 (cadr d-rands))
              (v3 (caddr d-rands)))
          (for ((w (in-set (γ v1))) #:when (addr? w))
            (let ((a (addr-a w)))
              (for ((ww (in-set (γ (store-lookup a)))))
                (when (hash? ww)
                  (store-update! a (α (hash-set ww v2 v3)))))))
          (set (α 'undefined)))))

    (define-native-prim! "vector-length"
      (lambda (_ κ d-rands)
        (if (= (length d-rands) 1)
            (let ((add-proc (lambda (x y)
                              (for/fold ((result ⊥)) ((prim2 (in-set (γ (cdr (assoc "+" lat-glob))))))
                                (⊔ result ((prim2-proc prim2) x y)))))
                  (lt-proc (lambda (x y)
                        (for/fold ((result ⊥)) ((prim2 (in-set (γ (cdr (assoc "<" lat-glob))))))
                          (⊔ result ((prim2-proc prim2) x y))))))
              (let ((v (for/fold ((v ⊥)) ((w (in-set (γ (car d-rands)))))
                         (match w
                           ((addr a)
                            (for/fold ((v v)) ((ww (γ (store-lookup a))))
                              (if (hash? ww)
                                  (⊔ v (for/fold ((n (α 0))) ((i (in-set (hash-keys ww))))
                                         (let ((ii (add-proc i (α 1))))
                                           (if (lt-proc ii n)
                                               n
                                               ii))))
                                  v)))
                           (_ v)))))
                (set v)))
            (set))))

        
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

    (define-native-prim! "eqv?"
      (lambda (_ __ d-rands)
        (set (for*/fold ((d ⊥)) ((w1 (γ (car d-rands))) (w2 (γ (cadr d-rands))))
               (⊔ d (match* (w1 w2)
                      (((addr a) (addr a))
                       (α #t))
                      (((addr _) (addr _))
                       (α #f))
                      ((_ _)
                       (α-eq? w1 w2))))))))

    
    (define-native-prim! "error"
      (lambda _ (set)))
    
    (define-native-prim! "display"
      (lambda (_ __ d-rands)
        (printf "~v\n" d-rands)
        (set (α 'undefined))))

    (include "primitives.rkt")
                                  
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

;  (define (prune s0 g pred?)
;
;    (define (remove-vertex g s)
;      (let ((S-succ (successors s g))
;            (S-pred (for/set (((s* S*) (in-hash g)) #:when (set-member? S* s))
;                      s*)))
;        (for/fold ((g g)) ((s-pred (in-set S-pred)))
;          (hash-set g s-pred (set-union (set-remove (hash-ref g s-pred) s) S-succ)))))
;    
;    (let loop ((S (set)) (W (set s0)) (g g))
;      (if (set-empty? W)
;          g
;          (let ((s (set-first W)))
;            (if (set-member? S s)
;                (loop S (set-rest W) g)
;                (if (pred? s)
;                    (let ((g* (remove-vertex g s)))
;                      (loop (set-add S s) (set-union (set-rest W) (hash-ref g* s (set))) g*))
;                    (loop (set-add S s) (set-union (set-rest W) (hash-ref g s (set))) g)))))))


  (define (compiled-state? s)
    (match s
      ((ev _ _ _ (cons rator _)) (set-member? Compiled rator))
      ((ko _ _ (cons rator _)) (set-member? Compiled rator))
      (_ #f)))

  (let ((t-start (current-milliseconds)))
    (let ((s0 (inject! e)))
      (explore! (set s0))
      (let ((t-end (current-milliseconds)))
        (let ((duration (- t-end t-start)))
          ;(printf "exploration ~v ms\n" duration)
          (system s0 g duration))))))

(define (result-state? s)
  (match s
    ((ko d '() #f)
     #t)
    (_
     #f)))
    
;(define (result-states g s0)
;  (let loop ((S (set)) (W (set s0)) (S-res (set)))
;    (if (set-empty? W)
;        S-res
;        (let ((s (set-first W)))
;          ;(printf "insp ~v ~v\n" (state->statei s) (set-map (hash-ref g s (set)) state->statei))
;          (if (set-member? S s)
;              (loop S (set-rest W) S-res)
;              (let ((S* (set-add S s))
;                    (S-succ (hash-ref g s (set))))
;                (if (result-state? s)
;                    (loop S* (set-union (set-rest W) S-succ) (set-add S-res s))
;                    (loop S* (set-union (set-rest W) S-succ) S-res))))))))

(define (evaluate e lat alloc kalloc)
  (let* ((sys (explore e lat alloc kalloc))
         (g (system-graph sys))
         (s0 (system-initial sys))
         (states (apply set-union (cons (list->set (hash-keys g)) (hash-values g))))
         (state-count (set-count states))
         (d-result (for/fold ((d (lattice-⊥ lat))) ((s (in-set states)) #:when (result-state? s))
                     ((lattice-⊔ lat) d (ko-d s)))))
    (printf "~v states in ~v ms\n" state-count (system-duration sys))
    (if (> state-count 10000)
        (printf "too many states: no graph generated\n")
        (generate-dot s0 g "grapho" (set-count states)))
    d-result))
    
(define (conc-alloc e κ)
  (count!))

(define (conc-kalloc rator rands ρ*)
  (cons rator (count!)))
                     
(define (conc-eval e)
  (evaluate e conc-lattice conc-alloc conc-kalloc))

(define (type-alloc e κ)
  e)

(define (type-kalloc rator rands)
  (cons rator rands))

(define (modf-kalloc rator rands ρ*)
  (cons («lam»-e0 (clo-e rator)) ρ*))

(define (type-eval e)
  (evaluate e type-lattice type-alloc modf-kalloc)) ; !!! MODF


(define (generate-dot s0 g name size)
  (define stateis (make-vector (add1 size)))
  (define (state->statei q) (index stateis q))
  (define ctxis (make-vector 2000))
  (define (ctx->ctxi q) (index ctxis q))

  (define (state-repr s)
    (match s
      ((ev e _ _ κ) (format "(ev ~a ~v)" (~a e #:max-width 40) (ctx->ctxi κ)))
      ((ko d _ κ) (format "(ko ~a ~v)" (~a d #:max-width 40) (ctx->ctxi κ)))))


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

;(type-eval
; (compile
;  (file->value "test/boyer.scm")
;))


(define (benchmark names)
  (printf "aac\n")
  (for ((name (in-list names)))
    (let* ((e (compile (file->value (string-append "test/" name ".scm"))))
           (sys (explore e type-lattice type-alloc modf-kalloc))
           (g (system-graph sys))
           (s0 (system-initial sys))
           (states (apply set-union (cons (list->set (hash-keys g)) (hash-values g))))
           (state-count (set-count states))
           (d-result (for/fold ((d (lattice-⊥ type-lattice))) ((s (in-set states)) #:when (result-state? s))
                     ((lattice-⊔ type-lattice) d (ko-d s)))))
      (printf "~a ~a ~a ~a\n" (~a name #:min-width 12) (~a state-count #:min-width 12) (~a (system-duration sys) #:min-width 12) (~a (set-count ((lattice-γ type-lattice) d-result)) #:min-width 4)))))

(benchmark (list ;"takr" "7.14" "triangl" "5.14.3"; unverified
            "fib" ;  warmup
            "collatz" ; warmup
            "5.14.3"
            "7.14"
            "browse"
            "churchnums"
            "dderiv"
            "deriv"
            "destruct"
            "fannkuch"
            "graphs"
            "grid"
            ;"matrix" no results in machine
            "mazefun"
            "mceval"
            "partialsums"
            "primtest"
            "regex"
            "scm2java"
            "spectralnorm"
            "treeadd"
            "triangl"
            "boyer"
            ))


