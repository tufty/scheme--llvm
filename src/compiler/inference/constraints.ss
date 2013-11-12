(library
 (compiler inference constraints)
 (export
  constraint?
  make-eq-constraint eq-constraint? eq-constraint-lhs eq-constraint-rhs)
 (import (rnrs) (compiler inference terms))  
 
 ;; Generic constraint
 (define-record-type constraint
   (nongenerative))

 ;; An equality constraint
 (define-record-type eq-constraint
   (parent constraint)
   (fields lhs rhs)
   (protocol
    (lambda (x)
      (lambda (l r)
        (if (and (term? l) (term? r))
            ((x l r))
            (error 'eq-constraint "non-term in constraint constructor" l r))))))

 )
