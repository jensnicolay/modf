(letrec ((_fib0 (lambda (_n1) (let ((_p2 (< _n1 2)))
									(if _p2 
									    _n1
									    (let ((_p3 (- _n1 1)))
									    	(let ((_p4 (_fib0 _p3)))
									    		(let ((_p5 (- _n1 2)))
									    			(let ((_p6 (_fib0 _p5)))
									    				(+ _p4 _p6))))))))))
	(_fib0 8))
