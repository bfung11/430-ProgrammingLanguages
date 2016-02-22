#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ5
  [numC (n : number)]
  [boolC (b : boolean)]
  [idC (id : symbol)]
  [stringC (str : string)]
  [ifC (condition : OWQQ5) 
       (if-true : OWQQ5) 
       (else-statement : OWQQ5)]
  [lamC (params : (listof symbol))
        (body : OWQQ5)]
  [binopC (op : symbol) ; operator
          (l : OWQQ5) 
          (r : OWQQ5)]
  [recC (name : symbol)
        (def : OWQQ5)
        (call : OWQQ5)]
  [appC (fn : OWQQ5) 
        (args : (listof OWQQ5))])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)]
  [stringV (str : string)]
  [cloV (params : (listof symbol))
        (body : OWQQ5)
        (env : Environment)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Keyword Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; given an operator and two OWQQ expressions
; returns the number as a Value after applying the operator to them
(define (do-arithmetic [op : (number number -> number)]) : (Value Value -> Value)
  (lambda ([left : Value]
           [right : Value])
    (cond 
      [(and (numV? left) (numV? right)) 
       (numV (op (numV-num left) (numV-num right)))]
      [else (error 'do-arithmetic "expects two numbers")])))

; given two OWQQ expressions
; returns the boolean as a Value after applying the operator to them
(define less-than-or-equal? : (Value Value -> Value)
  (lambda ([left : Value]
           [right : Value])
    (cond 
      [(and (numV? left) (numV? right)) 
       (boolV (<= (numV-num left) (numV-num right)))]
      [else (error 'less-than-or-equal? "expects two numbers")])))

; given two OWQQ expressions
; returns the number as a Value after applying the operator to them
(define is-equal? : (Value Value -> Value)
  (lambda ([left : Value]
           [right : Value])
    (cond 
      [(and (numV? left) (numV? right)) 
       (boolV (= (numV-num left) (numV-num right)))]
      [(and (boolV? left) (boolV? right)) 
       (boolV (eq? (boolV-bool left) (boolV-bool right)))]
      [(and (stringV? left) (stringV? right)) 
       (boolV (equal? (stringV-str left) (stringV-str right)))]
      [else (error 'do-arithmetic "expects two numbers or two booleans")])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Keyword Helper Function Test Cases
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test ((do-arithmetic +) (numV 4) (numV 4)) (numV 8))
(test ((do-arithmetic -) (numV 4) (numV 4)) (numV 0))
(test ((do-arithmetic *) (numV 4) (numV 4)) (numV 16))
(test ((do-arithmetic /) (numV 4) (numV 4)) (numV 1))
(test/exn ((do-arithmetic /) (boolV #t) (numV 4)) "expects two numbers")
(test/exn ((do-arithmetic /) (numV 4) (boolV #t)) "expects two numbers")

(test (less-than-or-equal? (numV 4) (numV 4)) (boolV #t))
(test (less-than-or-equal? (numV 4) (numV 5)) (boolV #t))
(test (less-than-or-equal? (numV 4) (numV 3)) (boolV #f))
(test/exn (less-than-or-equal? (boolV #t) (numV 4)) "expects two numbers")
(test/exn (less-than-or-equal? (numV 4) (boolV #t)) "expects two numbers")

(test (is-equal? (numV 4) (numV 4)) (boolV #t))
(test (is-equal? (numV 4) (numV 5)) (boolV #f))
(test (is-equal? (numV 4) (numV 3)) (boolV #f))
(test (is-equal? (boolV #t) (boolV #t)) (boolV #t))
(test (is-equal? (boolV #t) (boolV #f)) (boolV #f))
(test (is-equal? (boolV #f) (boolV #t)) (boolV #f))
(test (is-equal? (boolV #f) (boolV #f)) (boolV #t))
(test (is-equal? (stringV "hello") (stringV "hello")) (boolV #t))
(test (is-equal? (stringV "hello") (stringV "it's me")) (boolV #f))
(test/exn (is-equal? (boolV #t) (numV 4)) 
          "expects two numbers or two booleans")
(test/exn (is-equal? (numV 4) (boolV #t)) 
          "expects two numbers or two booleans")

;;;;;;;;;;;;;;;;;;;;;;;;
;
; Keywords
;
;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-table
  (hash (list (values '+ (do-arithmetic +))
              (values '- (do-arithmetic -))
              (values '* (do-arithmetic *))
              (values '/ (do-arithmetic /))
              (values '<= less-than-or-equal?)
              (values 'eq? is-equal?))))

(define id-keywords (list 'if 'true 'false 'func 'with  'array '<- '= 'begin))

;;;;;;;;;;;;;;;;;;;;;;;;
;
; Environments
;
;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-type-alias Environment (hashof symbol Value))
(define empty-env (hash empty))

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

; given a value and returns a string
; taken from Assignment 3 by John Clements
(define (serialize [value : Value]) : string
  (type-case Value value
    [numV (n) (to-string n)]
    [boolV (b) 
      (cond 
        [(equal? b #t) "true"]
        [else "false"])]
    [stringV (str) str]
    [cloV (p b e) "#<procedure>"]))

;;;;;;;;;;;;;;;;
;
; Interpreter
;
;;;;;;;;;;;;;;;;

; given and expression
; returns the interpreted value 
; taken from Assignment 3 by John Clements
(define (interp [expr : OWQQ5] 
                [env : Environment]) : Value
    (type-case OWQQ5 expr
      [numC (n) (numV n)]
      [boolC (b) (boolV b)]
      [binopC (s l r) 
        ((some-v (hash-ref binop-table s)) (interp l env) (interp r env))]
      [idC (id) 
        (type-case (optionof Value) (hash-ref env id)
          [none () (error 'interp "unbound identifier")]
          [some (val) val])]
      [stringC (str) (stringV str)]
      [ifC (c t f) (local [(define condition (interp c env))
                           (define then (interp t env))
                           (define els (interp f env))]
                     (type-case Value condition
                       [boolV (b) (if b then els)]
                       [else (error 'interp "expected boolean")]))] 
      [lamC (params body) (cloV params body env)]
      ; [recC (name rhs body)
      ;       (local [(define b (box (numV 12)))
      ;               (define new-env (cons (bind name b) env))
      ;               (define rhsval (interp rhs new-env))]
      ;         (begin (set-box! b rhsval)
      ;                (interp body new-env)))]))
      [appC (fn args) 
        (type-case Value (interp fn env)
          [cloV (params body env)
            (local [(define (interp-again expr) (interp expr env))
                    (define arg-vals (map interp-again args))
                    (define new-env (add-to-env params arg-vals env))]
              (interp body new-env))]
          [else (error 'interp "expected function")])]
      [else (error 'interp "not implemented")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Interpreter Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; interp before adding to env?
; function meant to add bindings to environment
; consumes a list of symbols, a list of Values and an environment and produces
; a list of Bindings
(define (add-to-env [params : (listof symbol)] 
                    [args : (listof Value)]
                    [env : Environment]) : Environment
  (cond 
    [(and (empty? params) (empty? args)) env]
    [else (add-to-env (rest params) 
                      (rest args) 
                      (hash-set env (first params) (first args)))]))

(test (add-to-env empty empty (hash empty))
      (hash empty))
(test (add-to-env (list 'x 'y 'z)
                  (list (numV 3)
                        (numV 5)
                        (numV 7))
                  empty-env)
      (hash (list (values 'x (numV 3))
                  (values 'y (numV 5))
                  (values 'z (numV 7)))))

;;;;;;;;;;;;;;;;;;;;
;
; Parser
;
;;;;;;;;;;;;;;;;;;;;

; given an s-expression
; returns an OWQQ expression
; taken from Assignment 5 by John Clements
(define (parse [s : s-expression]) : OWQQ5
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? `SYMBOL s) 
        (cond [(is-id-legal? (s-exp->symbol s)) (idC (s-exp->symbol s))]
              [else (error 'parse "not a valid symbol")])]
      [(s-exp-match? `STRING s) (stringC (s-exp->string s))]
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
            (cond 
              [(is-symbol-unique? sym-list)
                (appC (lamC sym-list (parse body))
                      (map parse fun-list))]
              [else (error 'parse "symbols not unique")]))]
      [(s-exp-match? '{func {SYMBOL ...} ANY} s)
        (local [(define a-list (s-exp->list s))
                (define params 
                        (map s-exp->symbol (s-exp->list (second a-list))))]
          (cond 
            [(is-symbol-unique? params) (lamC params (parse (third a-list)))]
            [else (error 'parse "params not unique")]))]
      [(s-exp-match? '{rec {SYMBOL = OWQQ5} OWQQ5} s)
        (local [(define a-list (s-exp->list s))
                (define fundef-list (s-exp->list (second a-list)))]
          (recC (s-exp->symbol (first fundef-list))
                (parse (third fundef-list))
                (parse (third a-list))))]
      [(s-exp-match? '{ANY ANY ...} s)
         (local [(define a-list (s-exp->list s))
                 (define first-elem (first a-list))]
          (cond [(and (s-exp-symbol? first-elem) 
                      (some? (hash-ref binop-table 
                                       (s-exp->symbol first-elem))))
                        (binopC (s-exp->symbol first-elem)
                                (parse (second a-list)) 
                                (parse (third a-list)))]
                [else (appC (parse first-elem)
                            (map parse (rest a-list)))]))]))

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

;;;;;;;;;;;;;;;;;;;;;;;;
;
; Top-eval Test Cases
;
;;;;;;;;;;;;;;;;;;;;;;;;

; tips : undefined;\n cannot reference an identifier before its definition
; tips : expected v. actual

(test (top-eval '{+ 12 4}) "16")
(test (top-eval '{* 12 4}) "48")
(test (top-eval '{- 12 4}) "8")
(test (top-eval '{/ 12 4}) "3")
(test (top-eval `true) "true")
(test (top-eval `false) "false")
(test (top-eval `"hello") "hello")
(test (top-eval '{if true 3 4}) "3")
(test (top-eval '{if true {+ 8 8} {+ 1 1}}) "16")
(test (top-eval '{{func {z y} {+ z y}} {+ 9 14} 98}) "121")
(test (top-eval '{with {z = {+ 9 14}}
                       {y = 98}
                       {+ z y}})
      "121")

;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Serialize Test Cases
;
;;;;;;;;;;;;;;;;;;;;;;;;;

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")
(test (serialize (cloV (list 'x 'y) (binopC '+ (numC 3) (numC 4)) empty-env)) 
                 "#<procedure>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Interpreter Test Cases
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(test (interp (binopC '<= (numC 3) (numC 3)) empty-env) 
      (boolV #t))
(test (interp (binopC '<= (numC 3) (numC 2)) empty-env) 
      (boolV #f))
(test (interp (binopC 'eq? (numC 3) (numC 3)) empty-env) 
      (boolV #t))
(test (interp (binopC 'eq? (numC 3) (numC 2)) empty-env) 
      (boolV #f))
(test (interp (binopC 'eq? (boolC #f) (boolC #f)) empty-env) 
      (boolV #t))
(test (interp (binopC 'eq? (boolC #t) (boolC #f)) empty-env) 
      (boolV #f))
(test (interp (binopC 'eq? (stringC "hello") (stringC "hello")) empty-env) 
      (boolV #t))
(test (interp (binopC 'eq? (stringC "hello") (stringC "it's me")) empty-env) 
      (boolV #f))
(test (interp (idC 'x)
              (hash (list (values 'x (numV 3))
                          (values 'y (numV 4)))))
      (numV 3))
(test (interp (stringC "hello") empty-env) (stringV "hello"))
(test (interp (ifC (boolC #t) (numC 4) (numC 5)) empty-env) (numV 4))
(test (interp (ifC (boolC #f) (numC 4) (numC 5)) empty-env) (numV 5))
(test/exn (interp (ifC (numC 3) (numC 4) (numC 5)) empty-env) 
          "expected boolean")
(test/exn (interp (idC 'x) empty-env) "unbound identifier")
(test (interp (lamC (list 'x 'y) (numC 3)) empty-env)
      (cloV (list 'x 'y) (numC 3) (hash empty)))
(test (interp (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
                    (list (binopC '+ (numC 9) (numC 14)) (numC 98))) 
              empty-env)
      (numV 121))
(test/exn (interp (appC (numC 3) empty) empty-env)
          "expected function")

;;;;;;;;;;;;;;;;;;;;;;
;
; Parser Test Cases
;
;;;;;;;;;;;;;;;;;;;;;;

; taken from Assignment 3 by John Clements
(test (parse '3) (numC 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse `x) (idC 'x))
(test (parse `"hello") (stringC "hello"))
(test/exn (parse '{+ if with})
          "not a valid symbol")
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


