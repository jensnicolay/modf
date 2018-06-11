(let ((_append-to-tail!7
       (lambda (_x8 _y9)
         (let ((_p38 (null? _x8)))
           (if _p38
               _y9
               (letrec ((_loop10 (lambda (_a11 _b12)
                                   (let ((_p39 (null? _b12)))
                                     (if _p39
                                         (let ((_$40 (set-cdr! _a11 _y9)))
                                           _x8)
                                         (let ((_p41 (cdr _b12)))
                                           (_loop10 _b12 _p41)))))))
                 (let ((_p42 (cdr _x8)))
                   (_loop10 _x8 _p42))))))))
  (let ((_destructive13 (lambda (_n14 _m15)
                          (letrec ((__loop017 (lambda (_i18 _a19)
                                                (let ((_p43 (= _i18 0)))
                                                  (if _p43
                                                      _a19
                                                      (let ((_p44 (- _i18 1)))
                                                        (let ((_p45 (cons '() _a19)))
                                                          (__loop017 _p44 _p45))))))))
                            (let ((_l16 (__loop017 10 '())))
                              (letrec ((__loop120 (lambda (_i21)
                                                    (let ((_p46 (= _i21 0)))
                                                      (if _p46
                                                          _l16
                                                          (let ((_p47 (car _l16)))
                                                            (let ((_p48 (null? _p47)))
                                                              (let ((_$86 (if _p48
                                                                              (letrec ((__loop222 (lambda (_l23)
                                                                                                    (let ((_p49 (null? _l23)))
                                                                                                      (if _p49
                                                                                                          '<undefined>
                                                                                                          (let ((_p50 (car _l23)))
                                                                                                            (let ((_p51 (null? _p50)))
                                                                                                              (let ((_$53 (if _p51
                                                                                                                              (let ((_p52 (cons '() '())))
                                                                                                                                (set-car! _l23 _p52))
                                                                                                                              '<unspecified>)))
                                                                                                                (let ((_p54 (car _l23)))
                                                                                                                  (letrec ((__loop324 (lambda (_j25 _a26)
                                                                                                                                        (let ((_p55 (= _j25 0)))
                                                                                                                                          (if _p55
                                                                                                                                              _a26
                                                                                                                                              (let ((_p56 (- _j25 1)))
                                                                                                                                                (let ((_p57 (cons '() _a26)))
                                                                                                                                                  (__loop324 _p56 _p57))))))))
                                                                                                                    (let ((_p58 (__loop324 _m15 '())))
                                                                                                                      (let ((_$59 (_append-to-tail!7 _p54 _p58)))
                                                                                                                        (let ((_p60 (cdr _l23))) (__loop222 _p60))))))))))))))
                                                                                (__loop222 _l16))
                                                                              (letrec ((__loop427 (lambda (_l128 _l229)
                                                                                                    (let ((_p61 (null? _l229)))
                                                                                                      (if _p61
                                                                                                          '<undefined>
                                                                                                          (letrec ((__loop530 (lambda (_j31 _a32)
                                                                                                                                (let ((_p62 (zero? _j31)))
                                                                                                                                  (if _p62
                                                                                                                                      _a32
                                                                                                                                      (let ((_$63 (set-car! _a32 _i21)))
                                                                                                                                        (let ((_p64 (- _j31 1)))
                                                                                                                                          (let ((_p65 (cdr _a32)))
                                                                                                                                            (__loop530 _p64 _p65)))))))))
                                                                                                            (let ((_p66 (car _l229)))
                                                                                                              (let ((_p67 (length _p66)))
                                                                                                                (let ((_p68 (quotient _p67 2)))
                                                                                                                  (let ((_p69 (car _l229)))
                                                                                                                    (let ((_p70 (__loop530 _p68 _p69)))
                                                                                                                      (let ((_p71 (car _l128)))
                                                                                                                        (let ((_p72 (length _p71)))
                                                                                                                          (let ((_n33 (quotient _p72 2)))
                                                                                                                            (let ((_p73 (= _n33 0)))
                                                                                                                              (let ((_p81 (if _p73
                                                                                                                                              (let ((_$74 (set-car! _l128 '())))
                                                                                                                                                (car _l128))
                                                                                                                                              (letrec ((__loop634 (lambda (_j35 _a36)
                                                                                                                                                                    (let ((_p75 (= _j35 1)))
                                                                                                                                                                      (if _p75
                                                                                                                                                                          (let ((_x37 (cdr _a36)))
                                                                                                                                                                            (let ((_$76 (set-cdr! _a36 '()))) _x37))
                                                                                                                                                                          (let ((_$77 (set-car! _a36 _i21)))
                                                                                                                                                                            (let ((_p78 (- _j35 1)))
                                                                                                                                                                              (let ((_p79 (cdr _a36)))
                                                                                                                                                                                (__loop634 _p78 _p79)))))))))
                                                                                                                                                (let ((_p80 (car _l128)))
                                                                                                                                                  (__loop634 _n33 _p80))))))
                                                                                                                                (let ((_$82 (set-cdr! _p70 _p81)))
                                                                                                                                  (let ((_p83 (cdr _l128)))
                                                                                                                                    (let ((_p84 (cdr _l229)))
                                                                                                                                      (__loop427 _p83 _p84))))))))))))))))))))
                                                                                (let ((_p85 (cdr _l16)))
                                                                                  (__loop427 _l16 _p85))))))
                                                                (let ((_p87 (- _i21 1)))
                                                                  (__loop120 _p87))))))))))
                                (__loop120 _n14)))))))
    (_destructive13 2 1)))
