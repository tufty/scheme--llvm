(import (nanopass)
	(match))

(define (constant? x)
  (or (boolean? x)
      (null? x)
      (fixnum? x)
      (flonum? x)
      (char? x)))

(define (datum? x)
  (or (constant? x)
      (and (pair? x) (datum? (car x)) (datum? (cdr x)))))

(define variable? symbol?)
(define (primitive? x)
  (memq x '(+ - cons car)))
(define (predicate? x)
  (memq x '(< <= = > >= eq? eqv? equal? null? false?)))


;; compiler infrastructure
(define (zip l1 l2)
  (fold-right (lambda (x y l) (cons (cons x y) l)) '() l1 l2))

(define (unzip x)
  (let loop ([x x] [l '()] [r '()])
    (cond [(null? x) (list (reverse l) (reverse r))]
	  [else (loop (cdr x) (cons (caar x) l) (cons (cdar x) r))])))

(define alist-cons
  (lambda (key val lst)
    (cons (cons key val) lst)))

(define alist-delete
  (lambda (key lst)
    (remp (lambda (e) (equal? key (car e))) lst)))

(define fresh
  (let ([count -1])
    (lambda (s)
      (set! count (+ count 1))
      (string->symbol (format "~a-~a" s count)))))


(define-syntax define-passes
  (syntax-rules ()
    [(_ p1 p2 ...) (zip '(p1 p2 ...) (list p1 p2 ...))]))

;; ===========================================================================
;; Here we start by preprocessing rnrs scheme into something more primitive that
;; we can work with
;; ===========================================================================

;; Base r6rs scheme language definition
(define-language L0
  (terminals
   (constant (c))
   (variable (x))
   (datum (d))
   (primitive (pp))
   (predicate (pr)))
  (entry Prog)
  (Prog ()
    (e* ...))
  (Expr (e body)
    c x pp pr
    (quote d)
    (define (x x* ...) body* ...)
    (define x e)
    (lambda (x* ...) body* ...)
    (if e0 e1 e2)
    (if e0 e1)
    (set! x e)
    (let ((x* e*) ...) body* ...)
    (let x ((x* e*) ...) body* ...)
    (let* ((x* e*) ...) body* ...)
    (letrec ((x* e*) ...) body* ...)
    (begin e* ...)
    (e0 e1 ...)))

(define-parser parse-L0 L0)

;; Scheme with bodies explicitly sequenced
(define-language L1
  (extends L0)
  (entry Prog)
  (Expr (e body)
    (- (define (x x* ...) body* ...)
       (lambda (x* ...) body* ...)
       (let ((x* e*) ...) body* ...)
       (let x ((x* e*) ...) body* ...)
       (let* ((x* e*) ...) body* ...)
       (letrec ((x* e*) ...) body* ...))
    (+ (define (x x* ...) body)
       (lambda (x* ...) body)
       (let ((x* e*) ...) body)
       (let x ((x* e*) ...) body)
       (let* ((x* e*) ...) body)
       (letrec ((x* e*) ...) body))))

(define-parser parse-L1 L1)

(define-pass make-begins-explicit : L0 (ir) -> L1 ()
#;  (Prog : Prog (ir) -> Prog ()
    [(,[e*] ...) 
     `(,e* ...)])
  (Expr : Expr (ir) -> Expr ()
    [(define (,x ,x* ...) ,[body*] ...)                `(define (,x ,x* ...) (begin ,body* ...))]
    [(lambda (,x* ...) ,[body*] ...)                   `(lambda (,x* ...) (begin ,body* ...))]
    [(let ((,x* ,[e*]) ...) ,[body*] ...)              `(let ((,x* ,e*) ...) (begin ,body* ...))]
    [(let ,x ((,x* ,[e*]) ...) ,[body*] ...)           `(let ,x ((,x* ,e*) ...) (begin ,body* ...))]
    [(let* ((,x* ,[e*]) ...) ,[body*] ...)             `(let* ((,x* ,e*) ...) (begin ,body* ...))]
    [(letrec ((,x* ,[e*]) ...) ,[body*] ...)           `(letrec ((,x* ,e*) ...) (begin ,body* ...))])
 #; (Prog ir))

;; As above, begins reduced
(define-language L2
  (extends L1)
  (entry Prog)
  (Expr (e body)
    (- (begin e* ...))
    (+ (begin e1 e2))))

(define-parser parse-L2 L2)

;; Gnarly fold to reduce multi-begins into pairs. 
(define-pass reduce-begins : L1 (ir) -> L2 ()
  (Expr : Expr (ir)-> Expr ()
    [(begin ,[e]) e]
    [(begin ,[e0] ,[e1]) `(begin ,e0 ,e1)]
    [(begin ,[e*] ...)
     (fold-right (lambda (a e) (if (null? e) a `(begin ,a ,e))) '() e*)]))

;; Reduce let forms into single lets only
(define-language L3
  (extends L2)
  (entry Prog)
  (Expr (e body)
    (- (let ((x* e*) ...) body)
       (let x ((x* e*) ...) body)
       (let* ((x* e*) ...) body)
       (letrec ((x* e*) ...) body))
    (+ (let ((x e)) body))))

(define-parser parse-L3 L3)

;; Similar to reducing begins.  Named let forms are converted direct to lambda calls.
(define-pass reduce-lets : L2 (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr ()
    [(let ((,x ,[e*]) ...) ,[body])
     (fold-right (lambda (x e l) `(let ((,x ,e)) ,l)) body x e*)]
    [(let ,x ((,x* ,[e*]) ...) ,[body])
     `(let ((,x (lambda (,x* ...) ,body))) (,x ,e* ...))]
    [(let* ((,x ,[e*]) ...) ,[body])
     (fold-right (lambda (x e l) `(let ((,x ,e)) ,l)) body x e*)]
    [(letrec ((,x* ,[e*]) ...) ,[body])
     (fold-right (lambda (x l) `(let ((,x undefined-value)) ,l))
		 (fold-right (lambda (x e l) `(begin (set! ,x ,e) ,l)) body x* e*) x*)]))

(define-language L4
  (extends L3)
  (entry Prog)
  (Expr (e body)
    (- (if e0 e1)
       (define (x x* ...) body))))

(define-parser parse-L4 L4)

;; Remove one-armed ifs and lambda defines
(define-pass remove-one-armed-ifs : L3 (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr ()
    [(if ,[e0] ,[e1]) `(if ,e0 ,e1 undefined-value)]
    [(define (,x ,x* ...) ,[body]) `(define ,x (lambda (,x* ...) ,body))]))

(define-language L5
  (extends L4)
  (entry Prog)
  (Expr (e body)
	(- (begin e1 e2))))

(define-parser parse-L5 L5)

;; desugar begin into let
(define-pass desugar-begin : L4 (ir) -> L5 ()
  (Expr : Expr (ir) -> Expr ()
	[(begin ,[e1] ,[e2])
	 (let ([t (fresh '_)])
	   `(let ([,t ,e1]) ,e2))]))
   
;; ===========================================================================
;; Now we make a transform into (nearly) Administrative Normal Form (ANF)
;; Transform taken and modified from http://matt.might.net/articles/a-normalization/
;; This is done outside the nanopass framework as it doesn't seem to be do-able from within
;; ===========================================================================

;; Base normalizer handles the following forms:
;; (lambda (x ...) exp)
;; (if exp exp exp)
;; (Fn exp ...)
;; V

;; We add the following in order to cover our base scheme:
;; (quote e)
;; (set! x e)

(define (abstraction? x)
  (and (pair? x) (equal? 'lambda (car x))))

(define (value? x) 
  (or (constant? x) (symbol? x)))

(define (normalize-term e)
  (normalize e (lambda (x) x)))

(define (normalize e k)
  (match e
    [`(lambda ,params ,body)   (k `(lambda ,params ,(normalize-term body)))]
    [`(define ,name ,body)     (k `(define ,name ,(normalize-term body)))]
    [`(if ,e1 ,e2 ,e3)         (normalize-name e1 (lambda (t) 
                                                    (k `(if ,t ,(normalize-term e2) ,(normalize-term e3)))))]
    [`(let ([,x ,e1]) ,e2)     (normalize e1 (lambda (n1) `(let ([,x ,n1]) ,(normalize e2 k))))]
    [`(,Fn . ,e*)	       (normalize-name  Fn (lambda (t)  (normalize-name* e* (lambda (t*) (k `(,t . ,t*))))))]

    [`(quote ,e)               (k `(quote ,e))]
    [`(set! ,x ,e)             (normalize-name x (lambda (t) (k `(set! ,t (normalize-term e)))))]
    [V (k V)]))

(define (normalize-name e k)
  (normalize e
             (lambda (N) 
               (if (value? N)
                   (k N)
                   (let ([t (fresh 't)])
		     `(let ([,t ,N]) ,(k t)))))))
;;                     `((lambda (,t) ,(k t)) ,N))))))

(define (normalize-name* e* k)
  (if (null? e*)
      (k '())
      (normalize-name (car e*)
                      (lambda (t)
                        (normalize-name* (cdr e*)
                                         (lambda (t*)
                                           (k `(,t . ,t*))))))))


(define (normalize-program x)
  (map normalize-term x))


(define (constant-or-variable? x)
  (or (constant? x) (variable? x)))

;; ===========================================================================
;; We now come back into the nanopass framework
;; We are in administrative normal form now except for if cases using a predicate
;; ===========================================================================
(define-language L8
  (terminals
   (constant (c))
   (datum (d))
   (variable (x))
   (constant-or-variable (cv))
   (primitive (pp))
   (predicate (pr)))
  (entry Prog)
  (Prog ()
    (e* ...))
  (Expr (e body)
        c x cv pp pr
	(lambda (x* ...) body) 
	(quote d)
	(define x e)
	(if e0 e1 e2) 
	(let ([x e]) body)
	(set! x e)
        (x cv* ...)))

(define-parser parse-L8 L8)

;; Wrap non-predicate if tests in test for false (and reverse conseq/alt)
;; Wrap non-test predicate applications in tests returning true or false
(define-pass predicafy-ifs : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
    [(if (,x ,cv* ...) ,[e1] ,[e2])
     (if (predicate? x)
	 `(if (,x ,cv* ...) ,e1 ,e2)
         (let ([name (fresh 't)])
           `(let ([,name (,x ,cv* ...)])
              (if (false? ,name) ,e2 ,e1))))]
    [(if ,[e0] ,[e1] ,[e2])
     `(if (false? ,e0) ,e2 ,e1)]
    [(,pr ,cv* ...) `(if (,pr ,cv* ...) #t #f)]))


;; Alpha renaming of all non-primitive symbols
(define-pass alpha-rename : L8 (ir) -> L8 ()
  (Expr : Expr (ir [bindings '()]) -> Expr ()
    ;; Lookup of rebound names
    [,x (let ([name (assq x bindings)])
	  (if name (cdr name) x))]
    [,cv (if (variable? cv)
             (let ([name (assq cv bindings)])
               (if name (cdr name) cv))
             cv)]
    ;; Lambda rebinds its formals
    [(lambda (,x* ...) ,body)
     (let ([names (map fresh x*)])
       `(lambda (,names ...) ,(Expr body (append (zip x* names) bindings))))]
    [(,x ,cv* ...)
     (let* ([n (assq x bindings)]
            [nx (if n (cdr n) x)]
            [n* (map (lambda (x) (if (variable? x) (assq x bindings) x)) cv*)]
            [nx* (map (lambda (x) (if x (cdr x) x)) n*)])
       `(,nx ,nx* ...))]
                
    ;; Set acts on something that already exists
    [(set! ,x ,[e])
     `(set! ,(Expr x bindings) ,e)]))

(define-language L9
  (extends L8)
  (entry Prog)
  (Expr (e body)
   (- (x cv* ...))
   (+ (prim-app pp cv* ...)
      (tail-prim-app pp cv* ...)
      (pred-app pr cv* ...)
      (tail-pred-app pr cv* ...)
      (app x cv* ...)
      (tail-app x cv* ...)
      (return c))))

(define-parser parse-L9 L9)

;; Here we detect tail applications and return values
(define-pass classify-applications : L8 (ir) -> L9 ()
  (Prog : Prog (ir) -> Prog ()
    [(,[e* #f -> e*] ... ,[e #t -> e]) `(,e* ... ,e)])
  (Expr : Expr (ir [tail #t]) -> Expr ()
    [(if ,e0 ,e1 ,e2)
     (let ([e00 (Expr e0 #f)]
           [e01 (Expr e1 tail)]
           [e02 (Expr e2 tail)])
       `(if ,e00 ,e01 ,e02))]
    [(let ([,x ,e]) ,body)
     (let ([e1 (Expr e #f)]
	   [b1 (Expr body tail)])
       `(let ([,x ,e1]) ,b1))]
    [(lambda (,x* ...) ,body)
     (let ([b0 (Expr body #t)])
       `(lambda (,x* ...) ,b0))]
    [(,pp ,cv* ...)
     (if tail
	 `(tail-prim-app ,pp ,cv* ...)
	 `(prim-app ,pp ,cv* ...))]
    [(,pr ,cv* ...)
     (if tail
	 `(tail-pred-app ,pr ,cv* ...)
	 `(pred-app ,pr ,cv* ...))]
    [(,x ,cv* ...)
     (if tail
	 `(tail-app ,x ,cv* ...)
	 `(app ,x ,cv* ...))]
    [,c
     (if tail
         `(return ,c)
         c)]
     

    ))  

(define-language L10
  (extends L9)
  (entry Prog)
  (Expr (e body)
    (- (lambda (x* ...) body))
    (+ (define-lambda x (x* ...) e)
       (nop))))

(define-parser parse-L10 L10)

;; Lift all lambdas to the top level
;; This breaks lexical scoping, which is nasty.
;; A better solution would be to handle top-level defines differently,
;; then treat inner defines as lets, and keep the let, alpha-renaming
;; references to the lambda to a fresh variable which is assigned in the
;; let form.  Later, maybe.
(define-pass lift-lambdas : L9 (ir) -> L10 ()
  (definitions
    (define lambdas '()))
  (Prog : Prog (ir) -> Prog ())
  (Expr : Expr (ir) -> Expr ()
    [(lambda (,x* ...) ,[body])
     (error 'lift-lambdas "unexpected lambda" ir)]
    [(let ((,x (lambda (,x* ...) ,[e0]))) ,[e1])
     (set! lambdas (cons `(define-lambda ,x (,x* ...) ,e0) lambdas))
     e1]
    [(define ,x (lambda (,x* ...) ,[e]))
     (set! lambdas (cons `(define-lambda ,x (,x* ...) ,e) lambdas))
     `(nop)])
  (let ([b (Prog ir)])
    ;; This is horrible.  Surely there's a better way to do this?
    (parse-L10 (append (map unparse-L10 lambdas) (unparse-L10 b))))
  )


;; Introduce types
(define (colon? x)
  (equal? x ':))
(define (larrow? x)
  (equal? x '<-))
(define (rarrow? x)
  (equal? x '->))
(define (primitive-type? x)
  (memq x '(i1 i8 i16 i32 float)))

(define-language L11
  (entry Prog)
  (terminals
    (constant (c))
    (number (n))
    (datum (d))
    (variable (x))
    (constant-or-variable (cv))
    (primitive (pp))
    (predicate (pr))
    (colon (:))
    (larrow (<-))
    (rarrow (->))
    (primitive-type (pt)))
  (Type (t)
    pt                 ;; primitive type
    (n t)              ;; sized array
    (t <- (t* ...))    ;; lambda type
    (t* ...)           ;; struct type
    (-> t)             ;; pointer type
   )
  (Typed-Expr (te)
    (t : e))
  (Prog (p)
    (te* ...))
  (Expr (e)
   (nop)
   (define-lambda x (x* ...) e)
   (return c)
   (tail-app x cv* ...)
   (app x cv* ...)
   (tail-pred-app pr cv* ...)
   (pred-app pr cv* ...)
   (tail-prim-app pp cv* ...)
   (prim-app pp cv* ...)
   c x cv pp pr
   (quote d)
   (define x e)
   (if e0 e1 e2)
   (let ([x0 e0]) e)
   (set! x e)))
  
#|
  
(define-pass analyze-types : L10 (ir) -> L11 ()
  ...
  (Prog : Prog (ir) -> * ()
    [(,e* ...) (for-each Expr e*)])
  (Expr 
  ...
)

  
;; Final pass outputting LLVM IR
#;
(define-pass to-llvm : Lx (ir) -> * ()
  (definitions
    (define code ""))
  (Prog : Prog (ir) -> * ()
    [(,e* ...)
     (for-each Expr e*)])
  (Expr : Expr (ir) -> * ()

  )
  (Prog ir)
  code
)

|#
;; ===========================================================================
;; Now "all" we have to do is string the various passes together and execute them 
;; ===========================================================================

(define compiler-passes
  (define-passes
    parse-L0 
    make-begins-explicit
    reduce-begins
    reduce-lets
    remove-one-armed-ifs
    desugar-begin
    unparse-L5
    normalize-program
   parse-L8
;;   predicafy-ifs
;;unparse-L8
;;    alpha-rename
    classify-applications
;;    unparse-L9
    lift-lambdas
    unparse-L10
    ))

(define compile
  (case-lambda 
   [() (compile '())]
   [(x) (compile x #f)]
   [(x debug?) 
    (let loop ([passes compiler-passes] [code x])
      (cond [(null? passes) code]
	    [else
	     (if debug? (display (format "*** Pass ~a\n*** Code ~a\n" (caar passes) code)))
	     (loop (cdr passes) ((cdar passes) code))]))]))
