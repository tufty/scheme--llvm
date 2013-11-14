(library
 (compiler inference lang)
 (export parse-L0 unparse-L0 L0? generate-constraints)
 (import (nanopass)
         (chezscheme)
         (only (srfi :1) alist-cons)
         (compiler inference terms)
         (compiler inference constraints))

 (define make-env list)

 (define (constant-type x)
   (cond
    [(number? x) (make-atomic-type-term 'number)]
    [(boolean? x) (make-atomic-type-term 'boolean)]
    [else (error 'constant-type "bad constant")]))
 
 (define (env-lookup x env)
   (cond [(assoc x env) => cdr]
         [else (error 'env-lookup "unbound variable" x env)]))

 (define (constant? x)
   (or (number? x) (boolean? x)))
 
 (define-language L0
   (terminals
    (symbol (x))
    (constant (c)))
   (Expr (e)
         x c
         (if e0 e1 e2)
         (lambda (x) e)
         (let (x e) e1)
         (begin e0 e1)
         (e0 e1)))

 (define-parser parse-L0 L0)
 
 (define generate-constraints
   (case-lambda
     [(exp) (generate-constraints exp (make-env))]
     [(exp env)
      (nanopass-case
       (L0 Expr) exp
       [,x (list (make-eq-constraint (make-expr-term x) (env-lookup x env)))]
       [,c (list (make-eq-constraint (make-expr-term c) (constant-type c)))]
       [(lambda (,x) ,e)
        (let ([tvar (make-typevar-term)])
          (append
           (generate-constraints e (alist-cons x tvar env))
           (list (make-eq-constraint (make-expr-term exp) (make-arrow-term tvar (make-expr-term e))))
           ))]
       [(if ,e0 ,e1 ,e2)
        (append
         (append
          (append
           (generate-constraints e0 env)
           (generate-constraints e1 env))
          (generate-constraints e2 env))
         (list
          (make-eq-constraint (make-expr-term e0) (make-atomic-type-term 'boolean))
          (make-eq-constraint (make-expr-term exp) (make-union-type-term (make-expr-term e1) (make-expr-term e2)))))]
       [(let (,x ,e) ,e1)
        (let ([tvar (make-typevar-term)])
          (append
           (append
            (append
             (list (make-eq-constraint (make-expr-term e) tvar))
             (generate-constraints e env))
            (generate-constraints e1 (alist-cons x tvar env)))
           (list (make-inst-constraint (make-expr-term exp) (make-expr-term e1)))))]
       [(begin ,e0 ,e1)
        (append
         (append
          (generate-constraints e0 env)
          (generate-constraints e1 env))
         (list (make-eq-constraint (make-expr-term exp) (make-expr-term e1))))]
       [(,e0 ,e1)
        (let ([tv (make-typevar-term)])
        (append
         (append (generate-constraints e0 env)
                 (generate-constraints e1 env))
         (list
          (make-inst-constraint tv (make-expr-term e0))
          (make-eq-constraint tv (make-arrow-term (make-expr-term e1) (make-expr-term exp))))))]
       )]))
 )
