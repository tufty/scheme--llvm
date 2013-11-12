(library
 (compiler inference substitution)
 (export new-substitution subs-lookup substitute subs-extend)
 (import (except (rnrs) assoc filter find fold-right for-each map member partition remove)
         (srfi :1) (compiler inference terms))

 (define new-substitution list)

 (define (subs-lookup t s)
   (find (lambda (x)
           (cond
            [(term=? (car x) t) x]
            [else #f]))
         s))

 (define (substitute t s)
   (cond
    [(subs-lookup t s) => cdr]
    [(arrow-term? t)
     (make-arrow-term (substitute (arrow-term-lhs t) s)
                      (substitute (arrow-term-rhs t) s))]
    [(constructed-type-term? t)
     (apply make-constructed-type-term
            (constructed-type-term-tag t)
            (map (lambda (x) (substitute x s)) (constructed-type-term-termlist t)))]
    [else t]))
 
 
 (define (subs-replace k v s)
   (map (lambda (x)
          (cons (term-replace k v (car x))
                (term-replace k v (cdr x))))
        s))
          
 (define (subs-extend k v s)
   (cons (cons k v)
         (subs-replace k v s)))

 )
