(let ((tree-node1 (lambda (v l r)
                    (let ((c1 (cons l r)))
                      (cons v c1)))))
  (letrec ((make-tree-nodes1 (lambda (levels)
                               (let ((c (<= levels 1)))
                                 (if c
                                     (tree-node1 1 'null 'null)
                                     (let ((levels* (- levels 1)))
                                       (let ((left (make-tree-nodes1 levels*)))
                                         (let ((right (make-tree-nodes1 levels*)))
                                           (tree-node1 1 left right)))))))))
    (letrec ((add-tree1 (lambda (node)
                          (let ((total (car node)))
                            (let ((leftright (cdr node)))
                              (let ((left (car leftright)))
                                (let ((lc (eq? left 'null)))
                                  (let ((ul (if lc
                                                #f
                                                (let ((total-left (add-tree1 left)))
                                                  (let ((total* (+ total total-left)))
                                                    (set! total total*))))))
                                    (let ((right (cdr leftright)))
                                      (let ((rc (eq? left 'null)))
                                        (let ((ur (if rc
                                                      #f
                                                      (let ((total-right (add-tree1 right)))
                                                        (let ((total* (+ total total-right)))
                                                          (set! total total*))))))
                                          total)))))))))))
      (let ((tree-node2 (lambda ()
                          (let ((c1 (cons 'null 'null)))
                            (cons 1 c1)))))
        (letrec ((create-tree2 (lambda (levels)
                                 (let ((c (= levels 0)))
                                   (if c
                                       'null
                                       (let ((n (tree-node2)))
                                         (let ((levels* (- levels 1)))
                                           (let ((lr (cdr n)))
                                             (let ((left (create-tree2 levels*)))
                                               (let ((ul (set-car! lr left)))
                                                 (let ((right (create-tree2 levels*)))
                                                   (let ((ur (set-cdr! lr right)))
                                                     n)))))))))))) 
          (letrec ((add-tree2 (lambda (node)
                                (let ((total (car node)))
                                  (let ((leftright (cdr node)))
                                    (let ((left (car leftright)))
                                      (let ((lc (eq? left 'null)))
                                        (let ((ul (if lc
                                                      #f
                                                      (let ((total-left (add-tree2 left)))
                                                        (let ((total* (+ total total-left)))
                                                          (set! total total*))))))
                                          (let ((right (cdr leftright)))
                                            (let ((rc (eq? left 'null)))
                                              (let ((ur (if rc
                                                            #f
                                                            (let ((total-right (add-tree2 right)))
                                                              (let ((total* (+ total total-right)))
                                                                (set! total total*))))))
                                                total)))))))))))
            (letrec ((create-tree3 (lambda (levels)
                                     (let ((c (= levels 0)))
                                       (if c
                                           'null
                                           (let ((n (cons 'null 'null)))
                                             (let ((levels* (- levels 1)))
                                               (let ((left (create-tree3 levels*)))
                                                 (let ((ul (set-car! n left)))
                                                   (let ((right (create-tree3 levels*)))
                                                     (let ((ur (set-cdr! n right)))
                                                       n))))))))))) 
              (letrec ((add-tree3 (lambda (node)
                                    (let ((total 1))
                                      (let ((left (car node)))
                                        (let ((lc (eq? left 'null)))
                                          (let ((ul (if lc
                                                        #f
                                                        (let ((total-left (add-tree3 left)))
                                                          (let ((total* (+ total total-left)))
                                                            (set! total total*))))))
                                            (let ((right (cdr node)))
                                              (let ((rc (eq? left 'null)))
                                                (let ((ur (if rc
                                                              #f
                                                              (let ((total-right (add-tree3 right)))
                                                                (let ((total* (+ total total-right)))
                                                                  (set! total total*))))))
                                                  total))))))))))
                (let ((tree1 (make-tree-nodes1 4)))
                  (let ((u1 (add-tree1 tree1)))
                    (let ((tree2 (create-tree2 4)))
                      (let ((u2 (add-tree2 tree2)))
                        (let ((tree3 (create-tree3 4)))
                          (add-tree3 tree3))))))))))))))



