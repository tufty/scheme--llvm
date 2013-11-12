(library
 (compiler inference)
 (export parse-L0 unparse-L0 generate-constraints unify pp)
 (import
  (except (chezscheme) assoc filter find fold-right for-each map member partition remove remove! append! make-list list-copy break reverse! last-pair iota)
  (srfi :1)
  (nanopass)
  (compiler inference constraints)
  (compiler inference terms)
  (compiler inference substitution)
  (compiler inference unification))

 (define (infer term) #f)

 (define make-env list)

 (define (constant-type x)
   (make-atomic-type-term 'number))
 
 (define (env-lookup x env)
   (cond [(assoc x env) => cdr]
         [else (error 'env-lookup "meh")]))

 (define-language L0
   (terminals
    (symbol (x))
    (number (c)))
   (Expr (e)
    x c
    (lambda (x) e)
    (e0 e1)))

 (define-parser parse-L0 L0)
 
 (define generate-constraints
   (case-lambda
     [(exp) (generate-constraints exp (make-env))]
     [(exp env)
      (nanopass-case
       (L0 Expr) exp
       [,x (list (make-eq-constraint (make-expr-term x) (make-var-term x)))]
       [,c (list (make-eq-constraint (make-expr-term c) (constant-type c)))]
       [(lambda (,x) ,e)
        (let ([tvar (make-var-term x)])
          (append
           (generate-constraints e env)
           (list (make-eq-constraint (make-expr-term exp) (make-arrow-term tvar (make-expr-term e))))
           ))]
       [(,e0 ,e1)
        (append
         (append (generate-constraints e0 env)
                 (generate-constraints e1 env))
;;         (list (make-eq-constraint (make-expr-term exp) (make-arrow-term (make-expr-term e1) (make-expr-term e0))))
         (list (make-eq-constraint (make-expr-term e0) (make-arrow-term (make-expr-term e1) (make-expr-term exp))))
         )])]))
        
                  

  (define (pp l)
    (cond
     [(list? l) (map pp l)]
     [(pair? l) `(,(pp (car l)) : ,(pp (cdr l)))]
     [(box? l) (pp (unbox l))]
     [(L0? l) (unparse-L0 l)]
     [(eq-constraint? l) `(,(pp (eq-constraint-lhs l)) = ,(pp (eq-constraint-rhs l)))]
     [(expr-term? l) (pp (expr-term-expr l))]
     [(var-term? l) (string->symbol (format "~a~a" #\x03a4 (pp (var-term-var l))))]
     [(typevar-term? l) (pp (typevar-term-name l))]
     [(atomic-type-term? l) (pp (atomic-type-term-type l))]
     [(arrow-term? l) `(,(pp (arrow-term-lhs l)) ,(string->symbol (string #\x21fe)) ,(pp (arrow-term-rhs l)))]
     [(constructed-type-term? l)
      (fold (lambda (x l) `(,@l ,(pp x))) `(,(constructed-type-term-tag l)) (constructed-type-term-termlist l))]
     [else l]))

 )
 
