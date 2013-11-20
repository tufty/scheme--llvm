(library
 (compiler inference lang)
 (export parse-L0 unparse-L0 L0? (rename (cg generate-constraints)))
 (import (nanopass)
         (chezscheme)
         (only (srfi :1) alist-cons fold)
         (compiler inference terms)
         (compiler inference constraints))

 ;; Hack!
 (include "cut.scm")
 
 (define make-env list)

 (define (env-lookup x env)
   (cond [(assoc x env) => cdr]
         [else (error 'env-lookup "unbound variable" x env)]))

 (define (constant? x)
   (or (boolean? x)
       (null? x)
       (fixnum? x)
       (flonum? x)
       (string? x)
       (char? x)))

 (define (constant-type c)
   (cond [(boolean? c) (make-atomic-type-term 'boolean)]
         [(null? c) (make-atomic-type-term 'null)]
         [(fixnum? c) (make-atomic-type-term 'fixnum)]
         [(flonum? c) (make-atomic-type-term 'flonum)]
         [(string? c) (make-atomic-type-term 'string)]
         [(char? c) (make-atomic-type-term 'char)]
         [else (error 'constant-type (format "unhandled constant type ~a" c))]))

 (define (datum? x)
   (or (constant? x)
       (symbol? x)
       (and (pair? x) (datum? (car x)) (datum? (cdr x)))))
 
 (define (datum-type d)
   (cond [(constant? d) (constant-type d)]
         [(symbol? d) (make-atomic-type-term 'symbol)]
         [(pair? d) (make-constructed-type-term 'pair (datum-type (car d)) (datum-type (cdr d)))]
         [else (error 'datum-type (format "unhandled datum type ~a" d))]))
 
 (define variable? symbol?)

 (define (primitive? x)
   (assoc x scheme-primitives))

 (define (primitive-type pr)
   (cond [(assoc pr scheme-primitives) => cdr]
         [else (error 'primitive-type "no type found for primitive" pr)]))

 (define scheme-primitives
   (map (lambda (x) (if (pair? x) x (cons x #f)))
        `((* . ,(T (^ ((list fixnum fixnum) -> fixnum) ((list flonum flonum) -> flonum))))
          (+ . ,(T ((list α α) -> α)))
          - ... / < <= = => > >= _ abs and append apply assoc assq assv begin
            binary-port? boolean=? boolean? bytevector bytevector-append
            bytevector-copy bytevector-copy! bytevector-length bytevector-u8-ref
            bytevector-u8-set! bytevector? caar cadr call-with-current-continuation
            call-with-port call-with-values call/cc car case cdar cddr cdr ceiling
            char->integer char-ready? char<=? char<? char=? char>=? char>? char?
            close-input-port close-output-port close-port complex? cond cond-expand
            cons current-error-port current-input-port current-output-port define
            define-record-type define-syntax define-values denominator do dynamic-wind
            else eof-object eof-object? eq? equal? eqv? error error-object-irritants
            error-object-message error-object? even? exact exact-integer-sqrt
            exact-integer? exact? expt features file-error? floor floor-quotient
            floor-remainder floor/ flush-output-port for-each gcd get-output-bytevector
            get-output-string guard if include include-ci inexact inexact?
            input-port-open? input-port? integer->char integer? lambda lcm length let
            let* let*-values let-syntax let-values letrec letrec* letrec-syntax list
            list->string list->vector list-copy list-ref list-set! list-tail list?
            make-bytevector make-list make-parameter make-string make-vector map max
            member memq memv min modulo negative? newline not null? number->string number?
            numerator odd? open-input-bytevector open-input-string open-output-bytevector
            open-output-string or output-port-open? output-port? pair? parameterize
            peek-char peek-u8 port? positive? procedure? quasiquote quote quotient raise
            raise-continuable rational? rationalize read-bytevector read-bytevector!
            read-char read-error? read-line read-string read-u8 real? remainder reverse
            round set! set-car! set-cdr! square string string->list string->number
            string->symbol string->utf8 string->vector string-append string-copy
            string-copy! string-fill! string-for-each string-length string-map string-ref
            string-set! string<=? string<? string=? string>=? string>? string? substring
            symbol->string symbol=? symbol? syntax-error syntax-rules textual-port?
            truncate truncate-quotient truncate-remainder truncate/ u8-ready? unless
            unquote unquote-splicing utf8->string values vector vector->list
            vector->string vector-append vector-copy vector-copy! vector-fill!
            vector-for-each vector-length vector-map vector-ref vector-set! vector? when
            with-exception-handler write-bytevector write-char write-string write-u8 zero?)))

 ;; A-Normalised language
 (define-language L0
   (terminals
    (variable (x))
    (constant (c))
    (datum (d))
    (primitive (pr)))
   (entry Expr)
   (Lambda-Formals (lf)
                   ;;    x (x* ...) (x* ... . x))
                   (x* ...))
   (Expr (e body)
         (let ([x* e*] ...) e)
         ae ce)
   (AExpr (ae)
          x c pr
          (quote d)
          (lambda lf e)
          (void))
   (CExpr (ce)
          (if ae e0 e1)
          (set! x e)
          (begin e0 e1)
          (ae ae* ...)))

 (define-parser parse-L0 L0)


 (define cg
   (case-lambda
     [(exp) (cg exp (make-env))]
     [(exp env)
      (define (cg-aexp exp env)
        (nanopass-case (L0 AExpr) exp
          [,pr
           `(,(make-ei-constraint (make-expr-term exp) (primitive-type pr)))]
          [,x 
           `(,(make-eq-constraint (make-expr-term exp) (env-lookup x env)))]
          [,c
           `(,(make-eq-constraint (make-expr-term exp) (constant-type c)))]
          [(quote ,d)
           `(,(make-eq-constraint (make-expr-term exp) (datum-type d)))]
          [(lambda (,x* ...) ,e)
           (let ([tvars (map (lambda (x) (make-typevar-term)) x*)]
                 [texprs (map make-expr-term x*)])
             `(,@(cg e (fold alist-cons env x* tvars))
               ,@(map make-eq-constraint texprs tvars)
               ,(make-eq-constraint (make-expr-term exp)
                                    (make-arrow-term
                                     (apply make-constructed-type-term 'list texprs)
                                     (make-expr-term e)))))]
          [(void)
           `(,(make-eq-constraint (make-expr-term exp) (make-atomic-type-term 'void)))]
          [else
           (error 'cg-aexp (format "Error generating constraints, invalid AExpr ~a" exp))]))
      (define (cg-cexp exp env)
        (nanopass-case (L0 CExpr) exp
          [(if ,ae ,e0 ,e1)
           `(,@(cg-aexp ae env)
             ,@(cg e0 env)
             ,@(cg e1 env)
             ,(make-eq-constraint (make-expr-term ae) (make-atomic-type-term 'boolean))
             ,(make-eq-constraint (make-expr-term exp) (make-union-type-term
                                                        (make-expr-term e0)
                                                        (make-expr-term e1))))]
          [(set! ,x ,e)
           (error 'cg-cexp "Error generating constraints, set! form not handled")]
          [(begin ,e0 ,e1)
           `(,@(cg e0 env)
             ,@(cg e1 env)
             ,(make-eq-constraint (make-expr-term exp) (make-expr-term e1)))]
          [(,ae ,ae* ...)
           (let ([tvar (make-typevar-term)]
                 [tvars (map (lambda (x) (make-typevar-term)) ae*)]
                 [texprs (map make-expr-term ae*)])
             `(,@(cg-aexp ae env)
               ,@(fold (lambda (e l) `(,@e ,@l)) '() (map (cut cg-aexp <> env) ae*))
               ,@(fold (lambda (e l) `(,e ,@l)) '() (map make-eq-constraint tvars texprs))
               ,(make-eq-constraint tvar (make-arrow-term
                                                         (apply make-constructed-type-term 'list tvars)
                                                         (make-expr-term exp)))
               ,(make-ii-constraint tvar (make-expr-term ae))))]
          [else (error 'cg-cexp (format "Error generating constraints, invalid CExpr ~a" exp))]))

      ;; Main entry point
      (nanopass-case (L0 Expr) exp
        [,ae (cg-aexp ae env)]
        [,ce (cg-cexp ce env)]
        [(let ([,x* ,e*] ...) ,e)
         (let* ([texprs (map make-expr-term e*)]
                [tvars (map (lambda (x) (make-typevar-term)) x*)]
                [new-env (fold alist-cons env x* tvars)])
           `(,@(map make-eq-constraint texprs tvars)
             ,@(fold (lambda (e l) `(,@e ,@l)) '() (map (cut cg <> new-env) e*))
             ,@(cg e new-env)
             ,(make-ii-constraint (make-expr-term exp) (make-expr-term e))))]
        [else (error 'cg (format "Error generating constraints, invalid Expr ~a" exp))])]))
             
   )
