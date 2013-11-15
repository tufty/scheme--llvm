(library
 (compiler inference terms)
 (export
  term? term=?
  make-expr-term expr-term? expr-term-expr
  make-typevar-term typevar-term? typevar-term-name
  make-atomic-type-term atomic-type-term? atomic-type-term-type
  make-constructed-type-term constructed-type-term? constructed-type-term-tag constructed-type-term-termlist
  make-arrow-term arrow-term? arrow-term-lhs arrow-term-rhs
  make-union-type-term union-type-term?
  make-intersection-type-term intersection-type-term?
  term-replace
  term-instantiate term-typevars
  )
 (import (except (chezscheme) assoc filter find fold-right for-each map member partition remove remove! append! make-list list-copy break reverse! last-pair iota)
         (srfi :1))

 ;; Horrible hack.
 (include "cut.scm")
 
 ;; Underlying term type
 (define-record-type term
   (nongenerative))
 
 ;; Expression terms
 ;; Boxes expression to allow for equality testing
 (define-record-type expr-term
   (parent term)
   (fields boxed-value)
   (protocol
    (lambda (x)
      (lambda (y)
        ((x (box y)))))))

 (define (expr-term-expr x)
   (and (expr-term? x)
        (unbox (expr-term-boxed-value x))))

 (define (expr-term=? a b)
   (and (expr-term? a) (expr-term? b)
        (equal? (expr-term-expr a) (expr-term-expr b))))

 ;; Infrastructure for typevars
 (define greeks
  '(#\x03b1 #\x03b2 #\x03b3 #\x03b4 #\x03b5 #\x03b6 #\x03b7 #\x03b8 #\x03b9 #\x03ba
    #\x03bb #\x03bc #\x03bd #\x03be #\x03bf #\x03c0 #\x03c1 #\x03c2 #\x03c3 #\x03c4
    #\x03c5 #\x03c6 #\x03c7 #\x03c8 #\x03c9))

 (define typevar-name
   (let ([count 0] [chars greeks])
     (lambda ()
       (let* ([c (if (null? chars) (+ 1 count) count)]
              [c* (if (null? chars) greeks chars)]
              [name (string->symbol (format "~A~A" (car c*) (fold string-append "" (map (lambda(x) (string #\x2032)) (iota c)))))])
         (set! count c)
         (set! chars (cdr c*))
         name))))      
 
 ;; Type variable term
 (define-record-type typevar-term
   (parent term)
   (fields name)
   (protocol
    (lambda (x)
      (lambda ()
        ((x (typevar-name)))))))

 (define (typevar-term=? a b)
   (and (typevar-term? a) (typevar-term? b)
        (equal? (typevar-term-name a) (typevar-term-name b))))

 ;; Base types
 (define-record-type atomic-type-term
   (parent term)
   (fields type)
   (protocol
    (lambda (x)
      (lambda (y)
        ((x y))))))

 (define (atomic-type-term=? a b)
   (and (atomic-type-term? a) (atomic-type-term? b)
        (equal? (atomic-type-term-type a) (atomic-type-term-type b))))

 ;; Constructed types
 (define-record-type constructed-type-term
   (parent term)
   (fields tag termlist)
   (protocol
    (lambda (x)
      (lambda (y . z)
        (if (and (symbol? y) (every term? z))
            ((x y z))
            (error 'constructed-type-term "non-term" y z))))))

 (define (constructed-type-term=? a b)
   (and (constructed-type-term? a) (constructed-type-term? b)
        (equal? (constructed-type-term-tag a) (constructed-type-term-tag b))
        (every equal? (constructed-type-term-termlist a) (constructed-type-term-termlist b))))

 (define (make-arrow-term l r)
   (make-constructed-type-term '-> l r))

 (define (arrow-term? x)
   (and (constructed-type-term? x)
        (equal? '-> (constructed-type-term-tag x))))

  (define (arrow-term-lhs x)
   (car (constructed-type-term-termlist x)))

 (define (arrow-term-rhs x)
   (cadr (constructed-type-term-termlist x)))

 (define uniq
   (lambda args
     (fold (lambda (x l)
             (if (find (lambda (y) (term=? y x)) l) l (cons x l))) '() args)))
 
 (define make-union-type-term
   (lambda rest
     (let ([unique-terms (apply uniq rest)])
       (if (= (length unique-terms) 1)
           (car unique-terms)
           (apply make-constructed-type-term 'U unique-terms)))))

 (define (union-type-term? x)
   (and (constructed-type-term? x)
        (equal? 'U (constructed-type-term-tag x))))

 (define (union-type-term=? a b)
   (cond
    [(and (union-type-term? a) (union-type-term? b))
     (constructed-type-term=? a b)]
    [(union-type-term? a)
     (any (cut term=? <> b) (constructed-type-term-termlist a))]
    [(union-type-term? b)
     (any (cut term=? <> a) (constructed-type-term-termlist b))]
    [else #f]))

 (define make-intersection-type-term
   (lambda rest
     (let ([unique-terms (apply uniq rest)])
       (if (= (length unique-terms) 1)
         (car unique-terms)
         (apply make-constructed-type-term '^ unique-terms)))))

 (define (intersection-type-term? x)
   (and (constructed-type-term? x)
        (equal? '^ (constructed-type-term-tag x))))

  (define (intersection-type-term=? a b)
   (cond
    [(and (intersection-type-term? a) (intersection-type-term? b))
     (constructed-type-term=? a b)]
    [(intersection-type-term? a)
     (every (cut term=? <> b) (constructed-type-term-termlist a))]
    [(intersection-type-term? b)
     (every (cut term=? <> a) (constructed-type-term-termlist b))]
    [else #f]))

 
 
 ;; Equality tester.  Must now take compatibility into account, particularly for
 ;; union and intersection types.
 (define (term=? a b)
   (or (expr-term=? a b)
       (typevar-term=? a b)
       (atomic-type-term=? a b)
 ;;      (union-type-term=? a b)
 ;;      (intersection-type-term=? a b)
       (constructed-type-term=? a b)
       ))

 ;; Replacement of terms
 (define (term-replace k v t)
   (cond
    [(term=? t k) v]
    [(union-type-term? t)
     (apply make-union-type-term
            (map (cut term-replace k v <>) (constructed-type-term-termlist t)))]
    [(intersection-type-term? t)
     (apply make-intersection-type-term
            (map (cut term-replace k v <>) (constructed-type-term-termlist t)))]
    [(constructed-type-term? t)
     (apply make-constructed-type-term
            (constructed-type-term-tag t)
            (map (cut term-replace k v <>) (constructed-type-term-termlist t)))]
    [else t]))

 ;; instantiation of terms
 (define (term-instantiate x env)
   (cond
    [(expr-term? x) x];(error 'term-instantiate "uninstantiable term ~a" x)]
    [(typevar-term? x) (cdr (assoc x env))]
    [(atomic-type-term? x) x]
    [(union-type-term? x)
     (apply make-union-type-term
            (map (cut term-instantiate <> env) (constructed-type-term-termlist x)))]
    [(intersection-type-term? x)
     (apply make-intersection-type-term
            (map (cut term-instantiate <> env) (constructed-type-term-termlist x)))]
    [(constructed-type-term? x)
     (apply make-constructed-type-term
            (constructed-type-term-tag x)
            (map (cut term-instantiate <> env) (constructed-type-term-termlist x)))]))

 (define (term-typevars x)
   (cond
    [(typevar-term? x) (list x)]
    [(constructed-type-term? x)
     (fold append '() (map term-typevars (constructed-type-term-termlist x)))]
    [else '()]))
 
 )
