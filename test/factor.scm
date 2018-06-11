(letrec ((_factor0 
          (lambda (_n1) 
            (let ((_extract-twos2 
                   (lambda (_n3) 
                     (letrec ((_loop4 
                               (lambda (_two-list5 _rest6) 
                                 (let ((_p14 (even? _rest6))) 
                                   (if _p14 
                                       (let ((_p15 (cons 2 _two-list5))) 
                                         (let ((_p16 (quotient _rest6 2))) 
                                           (_loop4 _p15 _p16))) 
                                       (cons _rest6 _two-list5)))))) 
                       (_loop4 '() _n3)))))
              (let ((_extract-odd-factors7 
                     (lambda (_partial-factorization8) 
                       (letrec ((_loop9 
                                 (lambda (_so-far10 _odd-product11 _trial-divisor12) 
                                   (let ((_p17 (* _trial-divisor12 _trial-divisor12))) 
                                     (let ((_p18 (< _odd-product11 _p17))) 
                                       (if _p18 
                                           (let ((_p19 (cons _odd-product11 _so-far10))) 
                                             (reverse _p19)) 
                                           (let ((_p20 (remainder _odd-product11 _trial-divisor12))) 
                                             (let ((_p21 (= _p20 0))) 
                                               (if _p21 
                                                   (let ((_p22 (cons _trial-divisor12 _so-far10))) 
                                                     (let ((_p23 (quotient _odd-product11 _trial-divisor12))) 
                                                       (_loop9 _p22 _p23 _trial-divisor12))) 
                                                   (let ((_p24 (+ _trial-divisor12 2))) 
                                                     (_loop9 _so-far10 _odd-product11 _p24)))))))))))
                         (let ((_p25 (cdr _partial-factorization8)))
                           (let ((_p26 (car _partial-factorization8))) 
                             (_loop9 _p25 _p26 3)))))))
                (let ((_partial-factorization13 (_extract-twos2 _n1))) 
                  (let ((_p27 (car _partial-factorization13))) 
                    (let ((_p28 (= _p27 1))) 
                      (if _p28 
                          (cdr _partial-factorization13) 
                          (_extract-odd-factors7 _partial-factorization13)))))))))) 
  (_factor0 35))