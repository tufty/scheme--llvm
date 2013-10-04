(library
 (compiler ts)
 (export
  ts:make-type-var ts:type-var?
  )
 (import (rnrs))

 (define (every pred list)              ; Simple definition.
   (let lp ((list list))                ; Doesn't return the last PRED value.
     (or (not (pair? list))
         (and (pred (car list))
              (lp (cdr list))))))

 
 (define-record-type (ts:type-var:base ts:type-var:make-base ts:type-var?)
   (fields 
    (mutable ts:type-var:constraints
             ts:type-var:constraints
             ts:type-var:set-constraints!))
   (protocol
    (lambda (x)
      (lambda ()
        (x '())))))
 
 (define-record-type (ts:type-var:atomic ts:type-var:make-atomic ts:type-var:atomic?)
   (parent ts:type-var:base)
   (fields
    (mutable ts:type-var:atomic:underlying-type
             ts:type-var:atomic:underlying-type
             ts:type-var:atomic:set-underlying-type!))
   (protocol
    (lambda (x)
      (lambda (t)
        ((x) t))))) 

 (define-record-type (ts:type-var:lambda ts:type-var:make-lambda ts:type-var:lambda?)
   (parent ts:type-var:base)
   (fields
    ts:type-var:lambda:return-type
    ts:type-var:lambda:argument-types)
   (protocol
    (lambda (x)
      (lambda (r a*)
        ((x) r a*)))))

 (define-record-type (ts:type-var:aggregate ts:type-var:make-aggregate ts:type-var:aggregate?)
   (parent ts:type-var:base)
   (protocol
    (lambda (x)
      (lambda ()
        ((x))))))

 (define-record-type (ts:type-var:vector ts:type-var:make-vector ts:type-var:vector?)
   (parent ts:type-var:aggregate)
   (fields
    ts:type-var:vector:count
    ts:type-var:vector:type-var)
   (protocol
    (lambda (x)
      (lambda (c t)
        ((x) c t)))))

 (define-record-type (ts:type-var:pair ts:type-var:make-pair ts:type-var:pair?)
   (parent ts:type-var:aggregate)
   (fields
    ts:type-var:vector:car
    ts:type-var:vector:cdr)
   (protocol
    (lambda (x)
      (lambda (c0 c1)
        ((x) c0 c1)))))

 ;; TODO add name and (key . type) for fields
 (define-record-type (ts:type-var:struct ts:type-var:make-struct ts:type-var:struct?)
   (parent ts:type-var:aggregate)
   (fields
    ts:type-var:struct:fields)
   (protocol
    (lambda (x)
      (lambda (f)
        ((x) f)))))


 (define ts:make-type-var
   (case-lambda
     [()     (ts:type-var:make-base)]
     [(x)    (ts:type-var:make-atomic x)]
     [rest
      (if (ts:type-var? (car rest))
          (ts:type-var:make-lambda (car rest) (cdr rest))
          (case (car rest)
            [(vector) (or (and (= (length rest) 3) (integer? (cadr rest)) (ts:type-var? (caddr rest))
                               (ts:type-var:make-vector (cadr rest) (caddr rest)))
                          (error 'ts:make-type "args should be ('vector <count> <type>)" rest))]
            [(pair)   (or (and (= (length rest) 3) (every ts:type-var? (cdr rest))
                               (ts:type-var:make-pair (cadr rest) (caddr rest)))
                          (error 'ts:make-type "args should be ('pair <type> <type>)" rest))]
            [(struct) (or (and (>= (length rest) 2) (every ts:type-var? (cdr rest))
                               (ts:type-var:make-struct (cdr rest)))
                          (error 'ts:make-type "args should be ('struct <type> ...)" rest))]
            [else     (error 'ts:make-type "unhandled syntax" rest)]
            ))]
      ))
 
 
 )
