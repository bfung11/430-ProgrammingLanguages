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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Parser Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))

(define id-keywords (list 'if 'true 'false 'fn 'with  'array '<- '= 'begin))

; given a symbol
; returns whether the symbol is a keyword or a binop
(define (is-id-legal? [sym : symbol]) : boolean
  (and (none? (hash-ref binop-table sym))
       (not (member sym id-keywords))))

(test (is-id-legal? 'if) #f)
(test (is-id-legal? 'a) #t)




