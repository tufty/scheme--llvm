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

(trace-define-pass make-begins-explicit : L0 (ir) -> L1 ()
  (Prog : Prog (ir) -> Expr ()
    [(,[e*] ...) 
     `(begin ,e* ...)])
  (Expr : Expr (ir) -> Expr ()
    [(define (,x ,x* ...) ,[body*] ...)                `(define (,x ,x* ...) (begin ,body* ...))]
    [(lambda (,x* ...) ,[body*] ...)                   `(lambda (,x* ...) (begin ,body* ...))]
    [(let ((,x* ,[e*]) ...) ,[body*] ...)              `(let ((,x* ,e*) ...) (begin ,body* ...))]
    [(let ,x ((,x* ,[e*]) ...) ,[body*] ...)           `(let ,x ((,x* ,e*) ...) (begin ,body* ...))]
    [(let* ((,x* ,[e*]) ...) ,[body*] ...)             `(let* ((,x* ,e*) ...) (begin ,body* ...))]
    [(letrec ((,x* ,[e*]) ...) ,[body*] ...)           `(letrec ((,x* ,e*) ...) (begin ,body* ...))])
  (Prog ir))

;; As above, begins reduced
(define-language L2
  (extends L1)
  (Expr (e body)
    (- (begin e* ...))
    (+ (begin e1 e2))))

(define-parser parse-L2 L2)

;; Gnarly fold to reduce multi-begins into pairs. 
(trace-define-pass reduce-begins : L1 (ir) -> L2 ()
  (Expr : Expr (ir)-> Expr ()
    [(begin ,[e]) e]
    [(begin ,[e0] ,[e1]) `(begin ,e0 ,e1)]
    [(begin ,[e*] ...)
     (fold-right (lambda (a e) (if (null? e) a `(begin ,a ,e))) '() e*)]))

;; Reduce let forms into single lets only
(define-language L3
  (extends L2)
  (Expr (e body)
    (- (let ((x* e*) ...) body)
       (let x ((x* e*) ...) body)
       (let* ((x* e*) ...) body)
       (letrec ((x* e*) ...) body))
    (+ (let ((x e)) body))))

(define-parser parse-L3 L3)

;; Similar to reducing begins.  Named let forms are converted direct to lambda calls.
(trace-define-pass reduce-lets : L2 (ir) -> L3 ()
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
  (Expr (e body)
    (- (if e0 e1)
       (define (x x* ...) body))))

(define-parser parse-L4 L4)

;; Remove one-armed ifs and lambda defines
(trace-define-pass remove-one-armed-ifs : L3 (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr ()
    [(if ,[e0] ,[e1]) `(if ,e0 ,e1 undefined-value)]
    [(define (,x ,x* ...) ,[body]) `(define ,x (lambda (,x* ...) ,body))]))

(define-language L5
  (extends L4)
  (Expr (e body)
	(- (begin e1 e2))))

(define-parser parse-L5 L5)

;; desugar begin into let
(trace-define-pass desugar-begin : L4 (ir) -> L5 ()
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

;; We produce subnormal form in the following case:
;; (if (pred? exp ...) exp exp) -> (if (pred? atom ...) exp exp) 

(define (abstraction? x)
  (and (pair? x) (equal? 'lambda (car x))))

(define (value? x) 
  (or (null? x) (constant? x) (symbol? x) (abstraction? x)))

(define (normalize-term e)
  (normalize e (lambda (x) x)))

(define (normalize e k)
  (match e
    [`(lambda ,params ,body)   (k `(lambda ,params ,(normalize-term body)))]
    [`(if ,e1 ,e2 ,e3)         (if (and (pair? e1) (predicate? (car e1)))
				   (normalize e1 (lambda (t) 
						   (k `(if ,t ,(normalize-term e2) ,(normalize-term e3)))))
				   (normalize-name e1 (lambda (t) 
							(k `(if ,t ,(normalize-term e2) ,(normalize-term e3))))))]
    [`(let ([,x ,e1]) ,e2)     (normalize e1 (lambda (n1) `(let ([,x ,n1]) ,(normalize e2 k))))]
    [`(,Fn . ,e*)              (if (primitive? Fn)
				   (normalize-name* e* (lambda (t*) (k `(,Fn . ,t*))))
				   (normalize-name  Fn (lambda (t)  (normalize-name* e* (lambda (t*) (k `(,t . ,t*)))))))]
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
  (normalize-term x))

;; ===========================================================================
;; We now come back into the nanopass framework
;; We are in administrative normal form now except for if cases using a predicate
;; ===========================================================================
(define-language L8
  (terminals
   (constant (c))
   (datum (d))
   (variable (x))
   (primitive (pp))
   (predicate (pr)))
  (Expr (e body)
        c x pp pr
	(lambda (x* ...) body) 
	(quote d)
	(define x e)
	(if e0 e1 e2) 
	(let ([x e]) body)
	(set! x e) 
	(e0 e1 ...)))

(define-parser parse-L8 L8)

;; Wrap non-predicate if tests in test for false (and reverse conseq/alt)
;; Wrap non-test predicate applications in tests returning true or false
(trace-define-pass predicafy-ifs : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
    [(if (,x ,[e*] ...) ,[e1] ,[e2])
     (if (predicate? x)
	 `(if (,x ,e* ...) ,e1 ,e2)
	 `(if (false? (,x ,e* ...)) ,e2 ,e1))]
    [(if ,[e0] ,[e1] ,[e2])
     `(if (false? ,e0) ,e2 ,e1)]
    [(,pr ,[e*] ...) `(if (,pr ,e* ...) #t #f)]))


;; Alpha renaming of all non-primitive symbols
(trace-define-pass alpha-rename : L8 (ir) -> L8 ()
  (Expr : Expr (ir [bindings '()]) -> Expr ()
    ;; Lookup of rebound names
    [,x (let ([name (assq x bindings)])
	  (if name (cdr name) x))]
    ;; Lambda rebinds its formals
    [(lambda (,x* ...) ,body)
     (let ([names (map fresh x*)])
       `(lambda (,names ...) ,(Expr body (append (zip x* names) bindings))))]
    [(,[e0] ,[e1] ...)
     `(,e0 ,e1 ...)]
    ;; Set acts on something that already exists
    [(set! ,x ,[e])
     `(set! ,(Expr x bindings) ,e)]))

;; We can now beta-reduce 
(trace-define-pass beta-reduce : L8 (ir) -> L8 ()
  (Expr : Expr (ir [bindings '()]) -> Expr ()
    [((lambda (,x* ...) ,body) ,c* ...)
     (let ([new-body (Expr body (append (zip x* c*) bindings))])
       (if (equal? new-body body) new-body (Expr new-body bindings)))]
    [,x (let ([name (assq x bindings)])
	  (if name (cdr name) x))]))

(define-language L9
  (extends L8)
  (Expr (e body)
   (- (e0 e1 ...))
   (+ (prim-app pp e* ...)
      (tail-prim-app pp e* ...)
      (pred-app pr e* ...)
      (tail-pred-app pr e* ...)
      (app e0 e* ...)
      (tail-app e0 e* ...))))

(define-parser parse-L9 L9)

(trace-define-pass classify-applications : L8 (ir) -> L9 ()
  (Expr : Expr (ir [tail #t]) -> Expr ()
    [(let ([,x ,e]) ,body)
     (let ([e1 (Expr e #f)]
	   [b1 (Expr body tail)])
       `(let ([,x ,e1]) ,b1))]
    [(lambda (,x* ...) ,body)
     (let ([b0 (Expr body #t)])
       `(lambda (,x* ...) ,b0))]
    [(,pp ,e* ...)
     (if tail
	 `(tail-prim-app ,pp ,e* ...)
	 `(prim-app ,pp ,e* ...))]
    [(,pr ,e* ...)
     (if tail
	 `(tail-pred-app ,pr ,e* ...)
	 `(pred-app ,pr ,e* ...))]
    [(,[e0] ,[e*] ...)
     (if tail
	 `(tail-app ,e0 ,e* ...)
	 `(app ,e0 ,e* ...))]
     

    ))  

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
    predicafy-ifs
    alpha-rename
    beta-reduce
    classify-applications
    unparse-L9))

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
