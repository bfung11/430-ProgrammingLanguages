#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ3
  [numC (n : number)]
  [boolC (b : boolean)]
  [idC (id : symbol)]
  [ifC (condition : OWQQ3) 
       (if-true : OWQQ3) 
       (else-statement : OWQQ3)]
  [lamC (params : (listof symbol))
        (body : OWQQ3)]
  [binopC (op : symbol) ; operator
          (l : OWQQ3) 
          (r : OWQQ3)]
  [appC (fn : OWQQ3) 
        (args : (listof OWQQ3))])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)]
  [cloV (params : (listof symbol))
        (body : OWQQ3)
        (env : Environment)])

; todo change environment to be a hash table
(define-type Binding
  [bind (name : symbol) (val : Value)])
 
(define-type-alias Environment (listof Binding))
(define empty-env empty)
(define extend-env cons)