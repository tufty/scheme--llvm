(library (compiler ts)
  (export
   ts:make-type ts:type?
   )
  (import (rnrs))

  (define-record-type (ts:type:base ts:type:make-base ts:type?)
    (nongenerative))

  (define-record-type (ts:type:atomic ts:type:make-atomic ts:type:atomic?)
    (nongenerative)
    (parent ts:type:base)
    (fields
     ts:type:atomic:underlying-type))

  (define-record-type (ts:type:lambda ts:type:make-lambda ts:type:lambda?)
    (nongenerative)
    (parent ts:type:base)
    (fields
     ts:type:lambda:return-type
     ts:type:lambda:argument-types))

  (define-record-type (ts:type:aggregate ts:type:make-aggregate ts:type:aggregate?)
    (nongenerative)
    (parent ts:type:base))

  (define-record-type (ts:type:vector ts:type:make-vector ts:type:vector?)
    (nongenerative)
    (parent ts:type:aggregate)
    (fields
     ts:type:vector:count
     ts:type:vector:type))

  (define-record-type (ts:type:pair ts:type:make-pair ts:type:pair?)
    (nongenerative)
    (parent ts:type:aggregate)
    (fields
     ts:type:vector:car
     ts:type:vector:cdr))

  (define ts:make-type
    (case-lambda
      [(x)    (ts:type:make-atomic x)]
      [(r a*) (ts:type:make-lambda r a*)]
      [rest
       (case (car rest)
         [(vector) (or (and (= (length rest) 3) (integer? (cadr rest)) (ts:type? (caddr rest))
                            (ts:type:make-vector (cadr rest) (caddr rest)))
                       (error 'ts:make-type "args should be ('vector <count> <type>)" rest))]
         [(pair)   (or (and (= (length rest) 3) (every ts:type? (cdr rest))
                            (ts:type:make-pair (cadr rest) (caddr rest)))
                       (error 'ts:make-type "args should be ('pair <type> <type>)" rest))]
         [else     (error 'ts:make-type "unhandled syntax" rest)]
         )]
      ))
      
  
  )
