(library
 (compiler inference unification)
 (export unify)
 (import
  (except (chezscheme) assoc filter find fold-right for-each map member partition remove remove! append! make-list list-copy break reverse! last-pair iota)
  (srfi :1)
  (compiler inference constraints)
  (compiler inference terms)
  (compiler inference substitution)
  (compiler inference pp))

 (define unify
   (case-lambda
     [(constraints)
      (unify constraints (new-substitution))]
     [(constraints theta)
      (cond
       [(null? constraints) theta]
       [else
        (let ([c (car constraints)])
;;          (display "===========\n")
;;          (display (pp constraints))(newline)
;;          (display "theta :\n")(display (pp theta))(newline)
          (cond
           [(eq-constraint? c)
            (let ([lhs (constraint-lhs c)]
                  [rhs (substitute (constraint-rhs c) theta)])
              (if (term=? lhs rhs)  ;; tautology
                  (unify (cdr constraints) theta)
                  (cond
                   ;; Expressions and typevars get looked up
                   [(or (expr-term? lhs) (typevar-term? lhs))
                    (cond
                     [(subs-lookup lhs theta)
                      => (lambda (x)
                           (unify (cons (make-eq-constraint (cdr x) rhs) (cdr constraints)) theta))]
                     [else (unify (cdr constraints) (subs-extend lhs rhs theta))])]
                   ;; Atomic types get reversed if necessary
                   [(atomic-type-term? lhs)
                    (cond
                     [(or (expr-term? rhs) (typevar-term? rhs))
                      (unify (cons (make-eq-constraint rhs lhs) (cdr constraints)) theta)]
                     [else
                      (error 'unify (format "types ~a and ~a do not unify in\n~a\n" (pp lhs) (pp rhs) (pp theta)))])]
                   ;; Constructed types similarly
                   [(constructed-type-term? lhs)
                    (cond
                     [(or (expr-term? rhs) (typevar-term? rhs))
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
                      (error 'unify (format "types ~a and ~a do not unify in\n~a\n" (pp lhs) (pp rhs) (pp theta)))])]
                   )))]
           [(inst-constraint? c)
            (let ([s (substitute (constraint-rhs c) theta)])
              (unify
               (cons (constraint-instantiate
                      (constraint-lhs c)
                      s)
                     (cdr constraints))
               theta))]

;;              (constraint-instantiate c) (cdr constraints)) theta)]
           [else (error 'unify "unhandled constraint type" c)]))])]))

 )
 
