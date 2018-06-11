(let ((main (lambda (_args3)
              (let ((_p15 (null? _args3)))
                (let ((_n4 (if _p15
                               1
                               (let ((_p16 (car _args3)))
                                 (string->number _p16)))))
                  (let ((_count5 0))
                    (let ((_flags6 (make-vector 192 0)))
                      (letrec ((_loop7 (lambda (_iter8)
                                         (let ((_p17 (> _iter8 0)))
                                           (if _p17
                                               (letrec ((__loop09 (lambda (_i10)
                                                                    (let ((_p18 (>= _i10 192)))
                                                                      (if _p18
                                                                          '<undefined>
                                                                          (let ((_$19 (vector-set! _flags6 _i10 #t)))
                                                                            (let ((_p20 (+ _i10 1)))
                                                                              (__loop09 _p20))))))))
                                                 (let ((_$21 (__loop09 0)))
                                                   (let ((_$22 (set! _count5 0)))
                                                     (letrec ((__loop111 (lambda (_i12)
                                                                           (let ((_p23 (>= _i12 192)))
                                                                             (if _p23
                                                                                 '<undefined>
                                                                                 (let ((_p24 (vector-ref _flags6 _i12)))
                                                                                   (let ((_$31 (if _p24
                                                                                                   (letrec ((__loop213 (lambda (_k14)
                                                                                                                         (let ((_p25 (>= _k14 192)))
                                                                                                                           (if _p25
                                                                                                                               '<undefined>
                                                                                                                               (let ((_$26 (vector-set! _flags6 _k14 #f)))
                                                                                                                                 (let ((_p27 (+ _k14 _i12)))
                                                                                                                                   (__loop213 _p27))))))))
                                                                                                     (let ((_p28 (+ _i12 _i12)))
                                                                                                       (let ((_$29 (__loop213 _p28)))
                                                                                                         (let ((_p30 (+ 1 _count5)))
                                                                                                           (set! _count5 _p30)))))
                                                                                                   '<unspecified>)))
                                                                                     (let ((_p32 (+ 1 _i12)))
                                                                                       (__loop111 _p32)))))))))
                                                       (let ((_$33 (__loop111 2)))
                                                         (let ((_p34 (- _iter8 1)))
                                                           (_loop7 _p34)))))))
                                               '<unspecified>)))))
                        (let ((_$35 (_loop7 _n4))) _count5)))))))))
  (main '()))
