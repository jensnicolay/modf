(let ((_phi5 (lambda (_x16 _x27 _x38 _x49)
               (let ((__t010 _x16))
                 (let ((_p23 (if __t010
                                 __t010
                                 (let ((__t111 (not _x27)))
                                   (if __t111
                                       __t111
                                       (not _x38))))))
                   (if _p23
                       (let ((__t212 (not _x27)))
                         (let ((_p24 (if __t212 __t212 (not _x38))))
                           (if _p24
                               (let ((__t313 _x49))
                                 (if __t313 __t313 _x27))
                               #f)))
                       #f))))))
  (let ((_try14 (lambda (_f15)
                  (let ((__t416 (_f15 #t)))
                    (if __t416
                        __t416
                        (_f15 #f))))))
    (let ((_sat-solve-417 (lambda (_p18)
                            (_try14 (lambda (_n119)
                                      (_try14 (lambda (_n220)
                                                (_try14 (lambda (_n321)
                                                          (_try14 (lambda (_n422)
                                                                    (_p18 _n119 _n220 _n321 _n422))))))))))))
      (_sat-solve-417 _phi5))))
