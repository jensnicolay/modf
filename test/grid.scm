(letrec ((_make-grid0 (lambda (_start0 _dims0) (let ((_v0 (let ((_35 (car _dims0))) (make-vector _35 _start0)))) (let ((_23 (cdr _dims0))) (let ((_24 (null? _23))) (let ((_25 (not _24))) (let ((_33 (if _25 (letrec ((_loop0 (lambda (_i0) (let ((_26 (car _dims0))) (let ((_27 (>= _i0 _26))) (if _27 #t (let ((_28 (cdr _dims0))) (let ((_29 (_make-grid0 _start0 _28))) (let ((_30 (vector-set! _v0 _i0 _29))) (let ((_31 _30)) (let ((_32 (+ _i0 1))) (_loop0 _32)))))))))))) (_loop0 0)) #t))) (let ((_34 _33)) _v0))))))))) (letrec ((_grid-ref0 (lambda (_g0 _n0) (let ((_17 (cdr _n0))) (let ((_18 (null? _17))) (if _18 (let ((_19 (car _n0))) (vector-ref _g0 _19)) (let ((_20 (car _n0))) (let ((_21 (vector-ref _g0 _20))) (let ((_22 (cdr _n0))) (_grid-ref0 _21 _22)))))))))) (letrec ((_grid-set!0 (lambda (_g1 _v1 _n1) (let ((_11 (cdr _n1))) (let ((_12 (null? _11))) (if _12 (let ((_13 (car _n1))) (vector-set! _g1 _13 _v1)) (let ((_14 (car _n1))) (let ((_15 (vector-ref _g1 _14))) (let ((_16 (cdr _n1))) (_grid-set!0 _15 _v1 _16)))))))))) (letrec ((_t0 (let ((_10 '(4 5 6))) (_make-grid0 0 _10)))) (letrec ((_u0 (let ((_9 '(2 2))) (_make-grid0 #f _9)))) (let ((_0 '(2 2 3))) (let ((_1 (_grid-ref0 _t0 _0))) (let ((_2 (equal? _1 0))) (if _2 (let ((_3 '24)) (let ((_4 '(2 2 3))) (let ((_5 (_grid-set!0 _t0 _3 _4))) (let ((_6 _5)) (let ((_7 '(2 2 3))) (let ((_8 (_grid-ref0 _t0 _7))) (equal? _8 24))))))) #f)))))))))
