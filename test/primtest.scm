(let ((_square9 
       (lambda (_x10) (* _x10 _x10)))) 
  (letrec ((_modulo-power11 
            (lambda (_base12 _exp13 _n14) 
              (let ((_p37 (= _exp13 0))) 
                (if _p37 
                    1 
                    (let ((_p38 (odd? _exp13))) 
                      (if _p38 
                          (let ((_p39 (- _exp13 1))) 
                            (let ((_p40 (_modulo-power11 _base12 _p39 _n14))) 
                              (let ((_p41 (* _base12 _p40))) 
                                (modulo _p41 _n14)))) 
                          (let ((_p42 (/ _exp13 2))) 
                            (let ((_p43 (_modulo-power11 _base12 _p42 _n14))) 
                              (let ((_p44 (_square9 _p43))) 
                                (modulo _p44 _n14))))))))))) 
    (let ((_is-trivial-composite?15 
           (lambda (_n16) 
             (let ((_p45 (modulo _n16 2))) 
               (let ((__t017 (= _p45 0))) 
                 (if __t017 __t017 
                     (let ((_p46 (modulo _n16 3))) 
                       (let ((__t118 (= _p46 0))) 
                         (if __t118 
                             __t118 
                             (let ((_p47 (modulo _n16 5))) 
                               (let ((__t219 (= _p47 0))) 
                                 (if __t219 
                                     __t219 
                                     (let ((_p48 (modulo _n16 7))) 
                                       (let ((__t320 (= _p48 0))) 
                                         (if __t320 
                                             __t320 
                                             (let ((_p49 (modulo _n16 11))) 
                                               (let ((__t421 (= _p49 0))) 
                                                 (if __t421 
                                                     __t421 
                                                     (let ((_p50 (modulo _n16 13))) 
                                                       (let ((__t522 (= _p50 0))) 
                                                         (if __t522 
                                                             __t522 
                                                             (let ((_p51 (modulo _n16 17))) 
                                                               (let ((__t623 (= _p51 0))) 
                                                                 (if __t623 
                                                                     __t623 
                                                                     (let ((_p52 (modulo _n16 19))) 
                                                                       (let ((__t724 (= _p52 0))) 
                                                                         (if __t724 
                                                                             __t724 
                                                                             (let ((_p53 (modulo _n16 23))) 
                                                                               (= _p53 0))))))))))))))))))))))))))))) 
      (letrec ((_is-fermat-prime?25 
                (lambda (_n26 _iterations27) 
                  (let ((__t828 (<= _iterations27 0))) 
                    (if __t828 
                        __t828 
                        (let ((_p54 (log _n26))) 
                          (let ((_p55 (log 2))) 
                            (let ((_p56 (/ _p54 _p55))) 
                              (let ((_byte-size29 (ceiling _p56)))
                                (let ((_a30 (%random _byte-size29))) 
                                  (let ((_p57 (- _n26 1))) 
                                    (let ((_p58 (_modulo-power11 _a30 _p57 _n26))) 
                                      (let ((_p59 (= _p58 1))) 
                                        (if _p59 
                                            (let ((_p60 (- _iterations27 1))) 
                                              (_is-fermat-prime?25 _n26 _p60)) 
                                            #f)))))))))))))) 
        (letrec ((_generate-fermat-prime31 
                  (lambda (_byte-size32 _iterations33) 
                    (let ((_n34 (%random _byte-size32))) 
                      (let ((_p61 (_is-trivial-composite?15 _n34))) 
                        (let ((_p62 (not _p61))) 
                          (let ((_p63 (if _p62 
                                          (_is-fermat-prime?25 _n34 _iterations33) 
                                          #f))) 
                            (if _p63 
                                _n34 
                                (_generate-fermat-prime31 _byte-size32 _iterations33))))))))) 
          (let ((_iterations35 10)) 
            (let ((_byte-size36 15)) 
              (_generate-fermat-prime31 _byte-size36 _iterations35))))))))