(library
 (compiler inference lang)
 (export parse-L0 unparse-L0 L0? generate-constraints)
 (import (nanopass)
         (chezscheme)
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
         [else (error 'env-lookup "meh")]))

 (define (constant? x)
   (or (number? x) (boolean? x)))
 
 (define-language L0
   (terminals
    (symbol (x))
    (constant (c)))
   (Expr (e)
         x c
         (lambda (x) e)
         (let (x e) e1)
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
       [(let (,x ,e) ,e1)
        (append
         (append
          (append
           (list (make-eq-constraint (make-expr-term e) (make-var-term x)))
           (generate-constraints e env))
          (generate-constraints e1 env))
         (list (make-eq-constraint (make-expr-term exp) (make-expr-term e1))))]
       [(,e0 ,e1)
        (append
         (append (generate-constraints e0 env)
                 (generate-constraints e1 env))
         ;;         (list (make-eq-constraint (make-expr-term exp) (make-arrow-term (make-expr-term e1) (make-expr-term e0))))
         (list (make-eq-constraint (make-expr-term e0) (make-arrow-term (make-expr-term e1) (make-expr-term exp))))
         )])]))
 
 )
