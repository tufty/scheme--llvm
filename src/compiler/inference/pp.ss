(library
 (compiler inference pp)
 (export pp)
 (import (except (chezscheme) assoc filter find fold-right for-each map member partition remove remove! append! make-list list-copy break reverse! last-pair iota)
         (srfi :1)
         (compiler inference terms)
         (compiler inference lang)
         (compiler inference constraints))

 (define (pp l)
   (cond
    [(list? l) (map pp l)]
    [(pair? l) `(,(pp (car l)) : ,(pp (cdr l)))]
    [(box? l) (pp (unbox l))]
    [(L0? l) (unparse-L0 l)]
    [(ei-constraint? l) `(,(pp (constraint-lhs l)) ≼ ,(pp (constraint-rhs l)))]
    [(ii-constraint? l) `(,(pp (constraint-lhs l)) ≤ ,(pp (constraint-rhs l)))]
    [(eq-constraint? l) `(,(pp (constraint-lhs l)) ≣ ,(pp (constraint-rhs l)))]
    [(expr-term? l) (pp (expr-term-expr l))]
    [(typevar-term? l) (pp (typevar-term-name l))]
    [(atomic-type-term? l) (pp (atomic-type-term-type l))]
    [(arrow-term? l) `(,(pp (arrow-term-lhs l)) ,(string->symbol (string #\x21fe)) ,(pp (arrow-term-rhs l)))]
    [(union-type-term? l)
     (fold (lambda (x l) (if (null? l) `(,(pp x)) `(,(pp x) ∪ ,@l))) '() (constructed-type-term-termlist l))]
    [(intersection-type-term? l)
     (fold (lambda (x l) (if (null? l) `(,(pp x)) `(,(pp x) ∩ ,@l))) '() (constructed-type-term-termlist l))]
    [(constructed-type-term? l)
     (fold (lambda (x l) `(,@l ,(pp x))) `(,(constructed-type-term-tag l)) (constructed-type-term-termlist l))]
    [else l]))
 )
