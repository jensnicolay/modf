(letrec ((fac (lambda (n) 
                (let ((t (= n 0))) 
                  (if t 
                      1 
                      (let ((u (- n 1))) 
                        (let ((v (fac u))) 
                          (* n v)))))))) 
  (fac 8))