;; Expected-result: 21
(let ((fib
       (lambda (n)
         (let ((a 0))
           (let ((b 1))
             (letrec ((loop
                       (lambda (x)
                         (let ((_10 (= x n)))
                           (if _10
                               a
                               (let ((olda a))
                                 (let ((_11 (set! a b)))
                                   (let ((_12
                                          (let ((_14 (+ olda b)))
                                            (let ((_13 _14)) (set! b _13)))))
                                     (let ((_15 (+ x 1)))
                                       (let ((_16 (loop _15))) _16))))))))))
               (loop 0)))))))
  (fib 8))
