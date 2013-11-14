(library
 (compiler inference constraints)
 (export
  constraint?  constraint-lhs constraint-rhs
  make-eq-constraint eq-constraint?
  make-inst-constraint inst-constraint? constraint-instantiate)
 (import (chezscheme)
         (compiler inference terms))  
 
 ;; Generic constraint
 (define-record-type constraint
   (fields lhs rhs)
   (nongenerative)
   (protocol
    (lambda (x)
      (lambda (l r)
        (if (and (term? l) (term? r))
            (x l r)
            (error 'eq-constraint "non-term in constraint constructor" l r))))))
        

 ;; An equality constraint
 (define-record-type eq-constraint
   (parent constraint)
   (protocol
    (lambda (x)
      (lambda (l r)
        ((x l r))))))

  ;; An equality constraint
 (define-record-type inst-constraint
   (parent constraint)
   (protocol
    (lambda (x)
      (lambda (l r)
        ((x l r))))))

 (define (constraint-instantiate lhs rhs)
   (let ([lhs-typevars (map (lambda (x) (cons x (make-typevar-term))) (term-typevars lhs))]
         [rhs-typevars (map (lambda (x) (cons x (make-typevar-term))) (term-typevars rhs))])
     (make-eq-constraint
      lhs
      (term-instantiate rhs rhs-typevars))))
         
 )
