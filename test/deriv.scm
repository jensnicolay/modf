(letrec ((_map0 (lambda (_f0 _l0) (let ((_46 (null? _l0))) (if _46 _l0 (let ((_47 (pair? _l0))) (if _47 (let ((_48 (car _l0))) (let ((_49 (_f0 _48))) (let ((_50 (cdr _l0))) (let ((_51 (_map0 _f0 _50))) (cons _49 _51))))) (error "Cannot map over a non-list")))))))) (letrec ((_deriv0 (lambda (_a0) (let ((_2 (pair? _a0))) (let ((_3 (not _2))) (if _3 (let ((_4 'x)) (let ((_5 (eq? _a0 _4))) (if _5 1 0))) (let ((_6 (car _a0))) (let ((_7 '+)) (let ((_8 (eq? _6 _7))) (if _8 (let ((_9 '+)) (let ((_10 (cdr _a0))) (let ((_11 (_map0 _deriv0 _10))) (cons _9 _11)))) (let ((_12 (car _a0))) (let ((_13 '-)) (let ((_14 (eq? _12 _13))) (if _14 (let ((_15 '-)) (let ((_16 (cdr _a0))) (let ((_17 (_map0 _deriv0 _16))) (cons _15 _17)))) (let ((_18 (car _a0))) (let ((_19 '*)) (let ((_20 (eq? _18 _19))) (if _20 (let ((_21 '*)) (let ((_22 '+)) (let ((_25 (cdr _a0))) (let ((_26 (_map0 (lambda (_a1) (let ((_23 '/)) (let ((_24 (_deriv0 _a1))) (list _23 _24 _a1)))) _25))) (let ((_27 (cons _22 _26))) (list _21 _a0 _27)))))) (let ((_28 (car _a0))) (let ((_29 '/)) (let ((_30 (eq? _28 _29))) (if _30 (let ((_31 '-)) (let ((_32 '/)) (let ((_33 (cadr _a0))) (let ((_34 (_deriv0 _33))) (let ((_35 (caddr _a0))) (let ((_36 (list _32 _34 _35))) (let ((_37 '/)) (let ((_38 (cadr _a0))) (let ((_39 '*)) (let ((_40 (caddr _a0))) (let ((_41 (caddr _a0))) (let ((_42 (caddr _a0))) (let ((_43 (_deriv0 _42))) (let ((_44 (list _39 _40 _41 _43))) (let ((_45 (list _37 _38 _44))) (list _31 _36 _45)))))))))))))))) (error "No derivation method available")))))))))))))))))))))))
                                                                                                                                                                                                                                                                           (letrec ((_result0 (let ((_1 '(+ (* 3 x x) (* a x x) (* b x) 5))) (_deriv0 _1)))) (let ((_0 '(+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x))) (* (* a x x) (+ (/ 0 a) (/ 1 x) (/ 1 x))) (* (* b x) (+ (/ 0 b) (/ 1 x))) 0))) (equal? _result0 _0)))))