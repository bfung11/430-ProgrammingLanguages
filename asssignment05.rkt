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

(define-type FundefC
  [fundef (name : symbol) 
          (params : (listof symbol)) 
          (body : OWQQ3)])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)]
  [cloV (params : (listof symbol))
        (body : OWQQ3)
        (env : Environment)])

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))

(define-type Binding
  [bind (name : symbol) (val : Value)])
 
(define-type-alias Environment (listof Binding))
(define empty-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;;;
;
; Top Level Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;

; given an expression
; returns a string after parsing and interpreting expression
; taken from Assignment 5 by John Clements
(define (top-eval [s : s-expression]) : string
  (serialize (interp (parse s) empty-env)))

; taken from Assignment 3 by John Clements
(test (top-eval '{+ 12 4}) "16")
(test (top-eval '{* 12 4}) "48")
(test (top-eval '{- 12 4}) "8")
(test (top-eval '{/ 12 4}) "3")
(test (top-eval `true) "true")
(test (top-eval `false) "false")
(test (top-eval '{if true 3 4}) "3")
(test (top-eval '{if true {+ 8 8} {+ 1 1}}) "16")
(test (top-eval '{{func {z y} {+ z y}} {+ 9 14} 98}) "121")
(test (top-eval '{with {z = {+ 9 14}}
                       {y = 98}
                       {+ z y}})
      "121")

; given a value and returns a string
; taken from Assignment 3 by John Clements
(define (serialize [value : Value]) : string
  (type-case Value value
    [numV (n) (to-string n)]
    [boolV (b) 
      (cond 
        [(equal? b #t) "true"]
        [else "false"])]
    [cloV (p b e) "#<procedure>"]))

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")
(test (serialize (cloV (list 'x 'y) (binopC '+ (numC 3) (numC 4)) empty-env)) 
                 "#<procedure>")

;;;;;;;;;;;;;;;;;;;;
;
; Parser
;
;;;;;;;;;;;;;;;;;;;;

; given an s-expression
; returns an OWQQ expression
; taken from Assignment 5 by John Clements
(define (parse [s : s-expression]) : OWQQ3
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? `SYMBOL s) 
        (cond [(some? (hash-ref binop-table (s-exp->symbol s))) 
               (error 'parse "not a valid symbol")]
              [else (idC (s-exp->symbol s))])]
      [(s-exp-match? `{if ANY ANY ANY} s) 
        (local [(define a-list (s-exp->list s))]
          (ifC (parse (second a-list)) 
               (parse (third a-list)) 
               (parse (fourth a-list))))]
      [(s-exp-match? '{with {SYMBOL = ANY} ... ANY} s)
        (local [(define a-list (s-exp->list s))
                ; take out with and body
                (define bind-list (reverse (rest (reverse (rest a-list)))))
                (define bind-as-list (map s-exp->list bind-list))
                (define sym-list (map s-exp->symbol (map first bind-as-list)))
                (define fun-list (map third bind-as-list))
                (define body (first (reverse (rest a-list))))]
          (appC (lamC sym-list (parse body))
                (map parse fun-list)))]
      [(s-exp-match? '{func {SYMBOL ...} ANY} s)
        (local [(define a-list (s-exp->list s))
                (define params 
                        (map s-exp->symbol (s-exp->list (second a-list))))]
          (lamC params (parse (third a-list))))]
      [(s-exp-match? '{ANY ANY ...} s)
         (local [(define a-list (s-exp->list s))
                 (define first-elem (first a-list))]
          (cond [(and (s-exp-symbol? first-elem) 
                      (some? (hash-ref binop-table (s-exp->symbol first-elem))))
                        (binopC (s-exp->symbol first-elem)
                                (parse (second a-list)) 
                                (parse (third a-list)))]
                [else (appC (parse first-elem)
                            (map parse (rest a-list)))]))]))

; taken from Assignment 3 by John Clements
(test (parse '3) (numC 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse `x) (idC 'x))
(test (parse '{if 1 2 3}) (ifC (numC 1) (numC 2) (numC 3)))
(test (parse '{func {} {+ 1 2}}) 
      (lamC empty (binopC '+ (numC 1) (numC 2))))
(test (parse '{func {x y} {+ x y}}) 
      (lamC (list 'x 'y) (binopC '+ (idC 'x) (idC 'y))))
(test (parse '{func {z y} {+ z y}})
      (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y))))
(test (parse '{{func {z y} {+ z y}} {+ 9 14} 98})
      (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
            (list (binopC '+ (numC 9) (numC 14)) (numC 98))))
(test (parse '{+ 3 3}) (binopC '+ (numC 3) (numC 3)))
(test (parse '{- 3 3}) (binopC '- (numC 3) (numC 3)))
(test (parse '{* 3 3}) (binopC '* (numC 3) (numC 3)))
(test (parse '{/ 3 3}) (binopC '/ (numC 3) (numC 3)))
(test (parse '{/ x 3}) (binopC '/ (idC 'x) (numC 3)))
(test (parse '{f 3 4}) (appC (idC 'f) (list (numC 3) (numC 4))))
(test (parse '{with {z = {+ 9 14}}
                    {y = 98}
                    {+ z y}})
      (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
            (list (binopC '+ (numC 9) (numC 14)) (numC 98))))

(test/exn (parse '{+ + +}) "not a valid symbol")
; (parse '{func {x x} 3}) (lamC ('x 'x))
; (parse '{+ if with})
; (parse 'func (x x) 3')
; expected exception on test expression: '(parse '(+ if with))
; Saving submission with errors.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Parser Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; given a symbol
; returns whether the symbol is a keyword or a binop
(define (is-id-legal? [sym : symbol]) : boolean
  (and (none? (hash-ref binop-table sym))
       (not (member sym id-keywords))))

(test (is-id-legal? 'if) #f)
(test (is-id-legal? 'a) #t)

; given a list of symbol
; returns whether or not there are duplicates in the list
(define (is-symbol-unique? [sym-list : (listof symbol)]) : boolean
  (cond 
    [(empty? sym-list) #t]
    [else (and (not (member (first sym-list) (rest sym-list)))
               (is-symbol-unique? (rest sym-list)))]))

(test (is-symbol-unique? (list 'a 'b 'a)) #f)
(test (is-symbol-unique? (list 'a 'b 'c)) #t)

;;;;;;;;;;;;;;;;
;
; Interpreter
;
;;;;;;;;;;;;;;;;

; given and expression
; returns the interpreted value 
; taken from Assignment 3 by John Clements
(define (interp [expr : OWQQ3] 
                [env : Environment]) : Value
    (type-case OWQQ3 expr
      [numC (n) (numV n)]
      [boolC (b) (boolV b)]
      [binopC (s l r) (binopC-to-NumV s (interp l env) (interp r env))]
      [idC (id) (lookup id env)]
      [ifC (c t f) (local [(define condition (interp c env))
                           (define then (interp t env))
                           (define els (interp f env))]
                     (type-case Value condition
                       [boolV (b) (if b then els)]
                       [else (error 'interp "expected boolean")]))] 
      [lamC (params body) (cloV params body env)]
      [appC (fn args) 
        (type-case Value (interp fn env)
          [cloV (params body env)
            (local [(define (interp-again expr) (interp expr env))
                    (define arg-vals (map interp-again args))
                    (define new-env (add-to-env params arg-vals env))]
              (interp body new-env))]
          [else (error 'interp "expected function")])]))

(test (interp (numC 3) empty-env) (numV 3))
(test (interp (numC 8) empty-env) (numV 8))
(test (interp (boolC #t) empty-env) (boolV #t))
(test (interp (boolC #f) empty-env) (boolV #f))
(test (interp (binopC '+ (numC 3) (numC 3)) empty-env) 
      (numV 6))
(test (interp (binopC '- (numC 3) (numC 3)) empty-env) 
      (numV 0))
(test (interp (binopC '* (numC 3) (numC 3)) empty-env) 
      (numV 9))
(test (interp (binopC '/ (numC 3) (numC 3)) empty-env) 
      (numV 1))
(test (interp (idC 'x)
              (list (bind 'x (numV 3))
                    (bind 'y (numV 4))))
      (numV 3))
(test (interp (ifC (boolC #t) (numC 4) (numC 5)) empty-env) (numV 4))
(test (interp (ifC (boolC #f) (numC 4) (numC 5)) empty-env) (numV 5))
(test/exn (interp (ifC (numC 3) (numC 4) (numC 5)) empty-env) 
          "expected boolean")
(test/exn (interp (idC 'x) empty-env) "unbound identifier")
(test (interp (lamC (list 'x 'y) (numC 3)) empty-env)
      (cloV (list 'x 'y) (numC 3) (list)))
(test (interp (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
                    (list (binopC '+ (numC 9) (numC 14)) (numC 98))) 
              empty-env)
      (numV 121))
(test/exn (interp (appC (numC 3) empty) empty-env)
          "expected function")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Interpreter Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; consumes a symbol and an environment and returns the number associated with 
; the symbol
; taken from PLAI, second edition by Shriram Krishnamurthi
(define (lookup [for : symbol] [env : Environment]) : Value
  (cond 
    [(empty? env) (error 'lookup "unbound identifier")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(test (lookup 'x 
              (list (bind 'x (numV 3))
                    (bind 'y (numV 4))))
      (numV 3))
(test (lookup 'y 
              (list (bind 'x (numV 3))
                    (bind 'y (numV 4))))
      (numV 4))

; given an operator and two OWQQ expressions
; returns the value after applying the operator to them
(define (binopC-to-NumV [op : symbol] [left : Value] [right : Value]) : Value
  (numV ((some-v (hash-ref binop-table op)) 
         (numV-num left)
         (numV-num right))))

(test (binopC-to-NumV '+ (numV 4) (numV 4)) (numV 8))
(test (binopC-to-NumV '* (numV 4) (numV 4)) (numV 16))
(test (binopC-to-NumV '- (numV 4) (numV 4)) (numV 0))
(test (binopC-to-NumV '/ (numV 4) (numV 4)) (numV 1))

; interp before adding to env?
; function meant to add bindings to environment
; consumes a list of symbols, a list of Values and an environment and produces
; a list of Bindings
(define (add-to-env [params : (listof symbol)] 
                    [args : (listof Value)]
                    [env : Environment]) : (listof Binding)
  (cond 
    [(and (empty? params) (empty? args)) empty]
    [else (cons (bind (first params) (first args)) 
                (add-to-env (rest params) (rest args) env))]))

(test (add-to-env (list 'x 'y 'z)
            (list (numV 3)
                  (numV 5)
                  (numV 7))
            empty-env)
      (list (bind 'x (numV 3))
            (bind 'y (numV 5))
            (bind 'z (numV 7))))





