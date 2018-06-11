(let ((_debug-trace0 (lambda () 'do-nothing))) 
  (let ((_cadr1 (lambda (_p2) 
                  (let ((_p63 (cdr _p2))) 
                    (car _p63))))) 
    (let ((_caddr3 (lambda (_p4) 
                     (let ((_p64 (cdr _p4))) 
                       (let ((_p65 (cdr _p64))) 
                         (car _p65)))))) 
      (let ((_regex-NULL5 #f)) 
        (let ((_regex-BLANK6 #t)) 
          (let ((_regex-alt?7 
                 (lambda (_re8) 
                   (let ((_p66 (pair? _re8))) 
                     (if _p66 
                         (let ((_p67 (car _re8))) 
                           (eq? _p67 'alt)) #f))))) 
            (let ((_regex-seq?9 
                   (lambda (_re10) 
                     (let ((_p68 (pair? _re10))) 
                       (if _p68 
                           (let ((_p69 (car _re10))) 
                             (eq? _p69 'seq)) #f))))) 
              (let ((_regex-rep?11 (lambda (_re12) 
                                     (let ((_p70 (pair? _re12))) 
                                       (if _p70 
                                           (let ((_p71 (car _re12))) 
                                             (eq? _p71 'rep)) #f))))) 
                (let ((_regex-null?13 (lambda (_re14) (eq? _re14 #f)))) 
                  (let ((_regex-empty?15 (lambda (_re16) (eq? _re16 #t)))) 
                    (let ((_regex-atom?17 (lambda (_re18) 
                                            (let ((__t019 (char? _re18))) 
                                              (if __t019 
                                                  __t019 
                                                  (symbol? _re18)))))) 
                      (let ((_match-seq20 (lambda (_re21 _f22) 
                                            (let ((_p72 (_regex-seq?9 _re21))) 
                                              (if _p72 
                                                  (let ((_p73 (_cadr1 _re21))) 
                                                    (let ((_p74 (_caddr3 _re21))) 
                                                      (_f22 _p73 _p74))) #f))))) 
                        (let ((_match-alt23 (lambda (_re24 _f25) 
                                              (let ((_p75 (_regex-alt?7 _re24))) 
                                                (if _p75 
                                                    (let ((_p76 (_cadr1 _re24))) 
                                                      (let ((_p77 (_caddr3 _re24))) 
                                                        (_f25 _p76 _p77))) #f))))) 
                          (let ((_match-rep26 (lambda (_re27 _f28) 
                                                (let ((_p78 (_regex-rep?11 _re27))) 
                                                  (if _p78 
                                                      (let ((_p79 (_cadr1 _re27))) (_f28 _p79)) #f))))) 
                            (let ((_seq29 (lambda (_pat130 _pat231) 
                                            (let ((_p80 (_regex-null?13 _pat130))) 
                                              (if _p80 
                                                  _regex-NULL5 
                                                  (let ((_p81 (_regex-null?13 _pat231))) 
                                                    (if _p81 
                                                        _regex-NULL5 
                                                        (let ((_p82 (_regex-empty?15 _pat130))) 
                                                          (if _p82 
                                                              _pat231 
                                                              (let ((_p83 (_regex-empty?15 _pat231))) 
                                                                (if _p83 
                                                                    _pat130 
                                                                    (let ((_p84 (cons _pat231 '()))) 
                                                                      (let ((_p85 (cons _pat130 _p84))) 
                                                                        (cons 'seq _p85)))))))))))))) 
                              (let ((_alt32 (lambda (_pat133 _pat234) 
                                              (let ((_p86 (_regex-null?13 _pat133))) 
                                                (if _p86 
                                                    _pat234 
                                                    (let ((_p87 (_regex-null?13 _pat234))) 
                                                      (if _p87 
                                                          _pat133 
                                                          (let ((_p88 (cons _pat234 '()))) 
                                                            (let ((_p89 (cons _pat133 _p88))) 
                                                              (cons 'alt _p89)))))))))) 
                                (let ((_rep35 (lambda (_pat36) 
                                                (let ((_p90 (_regex-null?13 _pat36))) 
                                                  (if _p90 
                                                      _regex-BLANK6 
                                                      (let ((_p91 (_regex-empty?15 _pat36))) 
                                                        (if _p91 
                                                            _regex-BLANK6 
                                                            (let ((_p92 (cons _pat36 '()))) 
                                                              (cons 'rep _p92))))))))) 
                                  (letrec ((_regex-empty37 (lambda (_re38) 
                                                             (let ((_p93 (_regex-empty?15 _re38))) 
                                                               (if _p93 
                                                                   #t 
                                                                   (let ((_p94 (_regex-null?13 _re38))) 
                                                                     (if _p94 
                                                                         #f 
                                                                         (let ((_p95 (_regex-atom?17 _re38))) 
                                                                           (if _p95 
                                                                               #f
                                                                               (let ((__t139 (_match-seq20 _re38 (lambda (_pat140 _pat241) 
                                                                                                                   (let ((_p96 (_regex-empty37 _pat140))) 
                                                                                                                     (let ((_p97 (_regex-empty37 _pat241))) 
                                                                                                                       (_seq29 _p96 _p97))))))) 
                                                                                 (if __t139 
                                                                                     __t139 
                                                                                     (let ((__t242 (_match-alt23 _re38 (lambda (_pat143 _pat244) 
                                                                                                                         (let ((_p98 (_regex-empty37 _pat143))) 
                                                                                                                           (let ((_p99 (_regex-empty37 _pat244))) 
                                                                                                                             (_alt32 _p98 _p99))))))) 
                                                                                       (if __t242 
                                                                                           __t242 
                                                                                           (let ((_p100 (_regex-rep?11 _re38))) 
                                                                                             (if _p100 
                                                                                                 #t 
                                                                                                 #f))))))))))))))) 
                                    (letrec ((_regex-derivative45 (lambda (_re46 _c47) 
                                                                    (let ((_$101 (_debug-trace0))) 
                                                                      (let ((_p102 (_regex-empty?15 _re46))) 
                                                                        (if _p102 
                                                                            _regex-NULL5 
                                                                            (let ((_p103 (_regex-null?13 _re46))) 
                                                                              (if _p103 
                                                                                  _regex-NULL5 
                                                                                  (let ((_p104 (eq? _c47 _re46))) 
                                                                                    (if _p104 
                                                                                        _regex-BLANK6 
                                                                                        (let ((_p105 (_regex-atom?17 _re46))) 
                                                                                          (if _p105 
                                                                                              _regex-NULL5 
                                                                                              (let ((__t348 (_match-seq20 _re46 (lambda (_pat149 _pat250) 
                                                                                                                                  (let ((_p106 (_regex-derivative45 _pat149 _c47))) 
                                                                                                                                    (let ((_p107 (_seq29 _p106 _pat250))) 
                                                                                                                                      (let ((_p108 (_regex-empty37 _pat149))) 
                                                                                                                                        (let ((_p109 (_regex-derivative45 _pat250 _c47)))
                                                                                                                                          (let ((_p110 (_seq29 _p108 _p109))) 
                                                                                                                                            (_alt32 _p107 _p110)))))))))) 
                                                                                                (if __t348 
                                                                                                    __t348 
                                                                                                    (let ((__t451 (_match-alt23 _re46 (lambda (_pat152 _pat253) 
                                                                                                                                        (let ((_p111 (_regex-derivative45 _pat152 _c47))) 
                                                                                                                                          (let ((_p112 (_regex-derivative45 _pat253 _c47))) 
                                                                                                                                            (_alt32 _p111 _p112))))))) 
                                                                                                      (if __t451 
                                                                                                          __t451 
                                                                                                          (let ((__t554 (_match-rep26 _re46 (lambda (_pat55) 
                                                                                                                                              (let ((_p113 (_regex-derivative45 _pat55 _c47))) 
                                                                                                                                                (let ((_p114 (_rep35 _pat55))) (_seq29 _p113 _p114))))))) 
                                                                                                            (if __t554 __t554 _regex-NULL5)))))))))))))))))) 
                                      (let ((_d/dc56 _regex-derivative45)) 
                                        (letrec ((_regex-match57 (lambda (_pattern58 _data59) 
                                                                   (let ((_p115 (null? _data59))) 
                                                                     (if _p115 
                                                                         (let ((_p116 (_regex-empty37 _pattern58))) 
                                                                           (_regex-empty?15 _p116)) 
                                                                         (let ((_p117 (car _data59))) 
                                                                           (let ((_p118 (_d/dc56 _pattern58 _p117))) 
                                                                             (let ((_p119 (cdr _data59))) 
                                                                               (_regex-match57 _p118 _p119))))))))) 
                                          (let ((_check-expect60 (lambda (_check61 _expect62) (equal? _check61 _expect62)))) 
                                            (let ((xx '(seq foo (rep bar))))
                                              (let ((yy '(foo bar)))
                                                (let ((_p120 (_regex-match57 xx yy))) 
                                                  (_check-expect60 _p120 #t))))))))))))))))))))))))))