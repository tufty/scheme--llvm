(library
 (compiler inference substitution)
 (export new-substitution subs-lookup substitute subs-extend)
 (import (chezscheme)
         (compiler inference terms))

 (include "cut.scm")

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
    [(union-type-term? t)
     (apply make-union-type-term
            (map (cut substitute <> s) (constructed-type-term-termlist t)))]
    [(constructed-type-term? t)
     (apply make-constructed-type-term
            (constructed-type-term-tag t)
            (map (cut substitute <> s) (constructed-type-term-termlist t)))]
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
