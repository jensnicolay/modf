    (define-compile-prim! "vector-copy"
      '(lambda (v)
         (let ((l (vector-length v)))
           (let ((v2 (make-vector l #f)))
             (letrec ((loop (lambda (i)
                              (let ((c (< i l)))
                                (if c
                                    (let ((x (vector-ref v i)))
                                      (let ((_ (vector-set! v2 i x)))
                                        (let ((ii (+ i 1)))
                                          (loop ii))))
                                    v2)))))
               (loop 0))))))
        
    (define-compile-prim! "equal?"
      '(lambda (x1 x2)
         (let ((_b_t2 (pair? x1)))
           (if _b_t2
               (let ((_b_t3 (pair? x2)))
                 (if _b_t3
                     (let ((_b_t4 (car x1)))
                       (let ((_b_t5 (car x2)))
                         (let ((_b_t6 (equal? _b_t4 _b_t5)))
                           (if _b_t6
                               (let ((_b_t7 (cdr x1)))
                                 (let ((_b_t8 (cdr x2)))
                                   (equal? _b_t7 _b_t8)))
                               #f))))
                     #f))
               (eq? x1 x2)))))

    (define-compile-prim! "cadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (car x))))

    (define-compile-prim! "cddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (cdr x))))

    (define-compile-prim! "caadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (car x)))
             (car y)))))

    (define-compile-prim! "caddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (car y)))))

    (define-compile-prim! "cadddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (let ((z (cdr y)))
               (car z))))))

    (define-compile-prim! "cdadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (car x)))
             (cdr y)))))

    (define-compile-prim! "cdddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (cdr y)))))

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

    (define-compile-prim! "memv"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (eqv? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (memv v d)))))))))

    (define-compile-prim! "memq"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (eq? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (memq v d)))))))))

    (define-compile-prim! "assq"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((key (car a)))
                   (let ((e (equal? key v)))
                     (if e
                         a
                         (let ((d (cdr lst)))
                           (assq v d))))))))))

    (define-compile-prim! "append"
      '(lambda (lst1 lst2)
         (let ((c (null? lst1)))
           (if c
               lst2
               (let ((d (cdr lst1)))
                 (let ((l (append d lst2)))
                   (let ((a (car lst1)))
                     (cons a l))))))))
                 
    (define-compile-prim! "length"
      '(lambda (lst)
         (let ((c (null? lst)))
           (if c
               0
               (let ((d (cdr lst)))
                 (let ((n (length d)))
                   (+ 1 n)))))))
    
    (define-compile-prim! "reverse"
      '(lambda (l)
         (letrec ((reverse-acc (lambda (l acc)
                                 (let ((c (null? l)))
                                   (if c
                                       acc
                                       (let ((u (cdr l)))
                                         (let ((v (car l)))
                                           (let ((w (cons v acc)))
                                             (reverse-acc u w)))))))))
           (reverse-acc l '()))))

    (define-compile-prim! "map"
      '(lambda (f lst)
         (let ((c (null? lst)))
           (if c
               lst
               (let ((a (car lst)))
                 (let ((x (f a)))
                   (let ((d (cdr lst)))
                     (let ((l (map f d)))
                       (cons x l)))))))))

    (define-compile-prim! "for-each"
      '(lambda (f lst)
         (let ((c (null? lst)))
           (if c
               'undefined
               (let ((a (car lst)))
                 (let ((_ (f a)))
                   (let ((d (cdr lst)))
                     (for-each f d))))))))    
    
    (define-compile-prim! "list?"
      '(lambda (v)
         (let ((c (null? v)))
           (if c
               #t
               (pair? v)))))

    (define-compile-prim! "list->string"
      '(lambda (lst) ; TODO `(apply string lst)` [requires apply]
         (let ((c (null? lst)))
           (if c
               ""
               (let ((ch (car lst)))
                 (let ((st (string ch)))
                   (let ((suf (cdr lst)))
                     (let ((sufst (list->string suf)))
                       (string-append st sufst)))))))))
    
    (define-compile-prim! "vector->list"
      '(lambda (vec)
           (letrec ((loop (lambda (i acc)
                            (let ((c (= i -1)))
                              (if c
                                  acc
                                  (let ((el (vector-ref vec i)))
                                    (let ((acc2 (cons el acc)))
                                      (let ((ii (- i 1)))
                                        (loop ii acc2)))))))))
             (let ((l (vector-length vec)))
               (let ((ll (- l 1)))
                 (loop ll '()))))))
    
    (define-compile-prim! "list->vector"
      '(lambda (lst)
         (letrec ((down (lambda (lst i)
                          (let ((c (null? lst)))
                            (if c
                                (let ((v (make-vector i #f)))
                                  v)
                                (let ((a (car lst)))
                                  (let ((d (cdr lst)))
                                    (let ((ii (+ i 1)))
                                      (let ((v (down d ii)))
                                        (let ((_ (vector-set! v i a)))
                                          v))))))))))
           (down lst 0))))
