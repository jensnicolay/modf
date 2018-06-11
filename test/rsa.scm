(letrec ((_extended-gcd0 
          (lambda (_a1 _b2) 
            (let ((_p42 (modulo _a1 _b2))) 
              (let ((_p43 (= _p42 0))) 
                (if _p43 
                    (cons 0 1) 
                    (let ((_p44 (modulo _a1 _b2))) 
                      (let ((_x:y3 (_extended-gcd0 _b2 _p44))) 
                        (let ((_x4 (car _x:y3))) 
                          (let ((_y5 (cdr _x:y3))) 
                            (let ((_p45 (quotient _a1 _b2))) 
                              (let ((_p46 (* _y5 _p45))) 
                                (let ((_p47 (- _x4 _p46))) 
                                  (cons _y5 _p47)))))))))))))) 
  (let ((_modulo-inverse6 
         (lambda (_a7 _n8) 
           (let ((_p48 (_extended-gcd0 _a7 _n8))) 
             (let ((_p49 (car _p48))) 
               (modulo _p49 _n8)))))) 
    (let ((_totient9 
           (lambda (_p10 _q11) 
             (let ((_p50 (- _p10 1))) 
               (let ((_p51 (- _q11 1))) 
                 (* _p50 _p51)))))) 
      (let ((_square12 
             (lambda (_x13) (* _x13 _x13)))) 
        (letrec ((_modulo-power14 
                  (lambda (_base15 _exp16 _n17) 
                    (let ((_p52 (= _exp16 0))) 
                      (if _p52 
                          1 
                          (let ((_p53 (odd? _exp16))) 
                            (if _p53 
                                (let ((_p54 (- _exp16 1))) 
                                  (let ((_p55 (_modulo-power14 _base15 _p54 _n17))) 
                                    (let ((_p56 (* _base15 _p55))) 
                                      (modulo _p56 _n17)))) 
                                (let ((_p57 (/ _exp16 2))) 
                                  (let ((_p58 (_modulo-power14 _base15 _p57 _n17))) 
                                    (let ((_p59 (_square12 _p58))) 
                                      (modulo _p59 _n17))))))))))) 
          (let ((_is-legal-public-exponent?18 
                 (lambda (_e19 _p20 _q21) 
                   (let ((_p60 (< 1 _e19))) 
                     (if _p60 
                         (let ((_p61 (_totient9 _p20 _q21))) 
                           (let ((_p62 (< _e19 _p61))) 
                             (if _p62 
                                 (let ((_p63 (_totient9 _p20 _q21))) 
                                   (let ((_p64 (gcd _e19 _p63))) 
                                     (= 1 _p64))) 
                                 #f))) 
                         #f))))) 
            (let ((_private-exponent22 
                   (lambda (_e23 _p24 _q25) 
                     (let ((_p65 (_is-legal-public-exponent?18 _e23 _p24 _q25))) 
                       (if _p65 
                           (let ((_p66 (_totient9 _p24 _q25))) 
                             (_modulo-inverse6 _e23 _p66)) 
                           (error "Not a legal public exponent for that modulus.")))))) 
              (let ((_encrypt26
                     (lambda (_m27 _e28 _n29) 
                       (let ((_p67 (> _m27 _n29))) 
                         (if _p67 
                             (error "The modulus is too small to encrypt the message.") 
                             (_modulo-power14 _m27 _e28 _n29)))))) 
                (let ((_decrypt30 
                       (lambda (_c31 _d32 _n33) 
                         (_modulo-power14 _c31 _d32 _n33)))) 
                  (let ((_p34 41)) 
                    (let ((_q35 47)) 
                      (let ((_n36 (* _p34 _q35))) 
                        (let ((_e37 7)) 
                          (let ((_d38 (_private-exponent22 _e37 _p34 _q35))) 
                            (let ((_plaintext39 42)) 
                              (let ((_ciphertext40 (_encrypt26 _plaintext39 _e37 _n36))) 
                                (let ((_decrypted-ciphertext41 (_decrypt30 _ciphertext40 _d38 _n36))) 
                                  (let ((_p68 (= _plaintext39 _decrypted-ciphertext41))) 
                                    (let ((_p69 (not _p68))) 
                                      (if _p69 
                                          (error "RSA fail!") 
                                          #t))))))))))))))))))))
