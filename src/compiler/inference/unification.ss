(library
 (compiler inference unification)
 (export unify)
 (import
  (except (rnrs) assoc filter find fold-right for-each map member partition remove)
  (srfi :1)
  (compiler inference constraints)
  (compiler inference terms)
  (compiler inference substitution)
  (compiler inference pp))

 (define unify
   (case-lambda
     [(constraints) (unify constraints (new-substitution))]
     [(constraints theta)
      (cond
       [(null? constraints) theta]
       [else
        (let ([c (car constraints)])
          (cond
           [(eq-constraint? c)
            (let ([lhs (eq-constraint-lhs c)]
                  [rhs (substitute (eq-constraint-rhs c) theta)])
              (if (term=? lhs rhs)  ;; tautology
                  (unify (cdr constraints) theta)
                  (cond
                   ;; Expressions and typevars get looked up
                   [(or (expr-term? lhs) (typevar-term? lhs) (var-term? lhs))
                    (cond
                     [(subs-lookup lhs theta)
                      => (lambda (x)
                           (unify (cons (make-eq-constraint (cdr x) rhs) (cdr constraints)) theta))]
                     [else (unify (cdr constraints) (subs-extend lhs rhs theta))])]
                   ;; For variables, we instantiate a new type variable and re-evaluate
                   ;; Shortcircuited to get basic inference working (see above condition)
                   [(var-term? lhs)
                    (let ([tv (make-typevar-term)])
                      (unify (append
                              (list (make-eq-constraint tv rhs))
                              (cdr constraints)) theta))]
                   ;; Atomic types get reversed if necessary
                   [(atomic-type-term? lhs)
                    (cond
                     [(or (expr-term? rhs) (typevar-term? rhs) (var-term? rhs))
                      (unify (cons (make-eq-constraint rhs lhs) (cdr constraints)) theta)]
                     [else
                      (error 'unify "types do not unify" (pp lhs) (pp rhs) (pp theta))])]
                   ;; Constructed types similarly
                   [(constructed-type-term? lhs)
                    (cond
                     [(or (expr-term? rhs) (typevar-term? rhs) (var-term? rhs))
                      (unify (cons (make-eq-constraint rhs lhs) (cdr constraints)) theta)]
                     [(and (constructed-type-term? rhs) (equal? (constructed-type-term-tag lhs)
                                                                (constructed-type-term-tag rhs)))
                      (unify (append
                              (map make-eq-constraint
                                   (constructed-type-term-termlist lhs)
                                   (constructed-type-term-termlist rhs))
                              (cdr constraints))
                             theta)]
                     [else
                      (error 'unify "types do not unify"  (pp lhs) (pp rhs) (pp theta))])]                 
                   )))]
           [else (error 'unify "unhandled constraint type" c)]))])]))

 )
 
