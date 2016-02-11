#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ4
  [numC (n : number)]
  [boolC (b : boolean)]
  [idC (id : symbol)]
  [arrayC (elements : (listof OWQQ4))]
  [ifC (condition : OWQQ4) 
       (if-true : OWQQ4) 
       (else-statement : OWQQ4)]
  [lamC (params : (listof symbol))
        (body : OWQQ4)]
  [binopC (op : symbol) ; operator
          (l : OWQQ4) 
          (r : OWQQ4)]
  [appC (fn : OWQQ4) 
        (args : (listof OWQQ4))])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)]
  [cloV (params : (listof symbol))
        (body : OWQQ4)
        (env : Environment)]
  [nullV])

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Environment Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type-alias Location number)

(define-type Binding
  [binding (name : symbol) (val : Location)])
 
(define-type-alias Environment (listof Binding))
(define empty-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Store Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Sbind
  [sbind (location : Location) (value : Value)])

(define-type-alias Store (listof Sbind))
(define empty-store empty)
(define override-store cons)

(define-type Result
  [v*s (v : Value) (s : Store)])

;;;;;;;;;;;;;;;;;;;;;;;
;
; Monad Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;

(define-type-alias (Computation 'a) (Store -> Result))

;;;;;;;;;;;;;;;;;;;;
;
; Parser
;
;;;;;;;;;;;;;;;;;;;;

(define empty-array 1)

; Parses an expression.
; expected vs. actual
; taken from Assignment 3 by John Clements
(define (parse [s : s-expression]) : OWQQ4
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? '{array ANY ...} s)
        (local [(define a-list (s-exp->list s))]
          (cond 
            [(= (length a-list) empty-array) (arrayC empty)]
            [else (arrayC (map parse (rest a-list)))]))]
      [(s-exp-match? `SYMBOL s) 
        (cond [(some? (hash-ref binop-table (s-exp->symbol s))) 
               (error 'parse "not a valid symbol")]
              [else (idC (s-exp->symbol s))])]
      ; [(s-exp-match `{new-array OWQQ4 OWQQ4} s)
      ;   (local [(define a-list (s-exp->list s))]
      ;     (parse (second s)) (parse (third s))
      ;     )]

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
; question how to parse new forms like array and set?
(test (parse '3) (numC 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse `x) (idC 'x))
(test (parse '{array})
      (arrayC empty))
(test (parse '{array 3 false {+ 3 2} x})
      (arrayC (list (numC 3) 
                    (boolC #f) 
                    (binopC '+ (numC 3) (numC 2))
                    (idC 'x))))
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

;;;;;;;;;;;;;;;;;;;;
;
; Interpreter
;
;;;;;;;;;;;;;;;;;;;;

; consumes a symbol and an environment and returns the number associated with 
; the symbol
; taken from 
; Programming Languages: Application and Interpretation, 
; by Shriram Krishnamurthi, second edition.
; (define (lookup [for : symbol] [env : Environment]) : Value
;   (cond 
;     [(empty? env) (error 'lookup "unbound identifier")]
;     [else (cond
;             [(symbol=? for (binding-name (first env)))
;              (binding-val (first env))]
;             [else (lookup for (rest env))])]))

; (test (lookup 'x 
;               (list (binding 'x (numV 3))
;                     (binding 'y (numV 4))))
;       (numV 3))
; (test (lookup 'y 
;               (list (binding 'x (numV 3))
;                     (binding 'y (numV 4))))
;       (numV 4))

; consumes an operator a left and right value for a binopC and returns the
; resulting value
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
; (define (add-to-env [params : (listof symbol)] 
;                     [args : (listof Value)]
;                     [env : Environment]) : (listof Binding)
;   (cond 
;     [(and (empty? params) (empty? args)) empty]
;     [else (cons (binding (first params) (first args)) 
;                 (add-to-env (rest params) (rest args) env))]))

; (test (add-to-env (list 'x 'y 'z)
;             (list (numV 3)
;                   (numV 5)
;                   (numV 7))
;             empty-env)
;       (list (binding 'x (numV 3))
;             (binding 'y (numV 5))
;             (binding 'z (numV 7))))

; alpha-computation = (Store -> (alpha * Store))
; (Value -> ((listof Sbind) -> Result))
; debugging - expected v. actual

; (Value -> (Store -> Value*Store))
(define (lift [v : 'a])  : (Computation 'a)
  (lambda ([sto : Store]) (v*s v sto)))

(define (bind [a : (Computation 'a)]
              [b : ('a -> (Computation 'b))]) : (Computation 'b)
  (lambda ([sto : Store])
    (type-case Result (a sto)
      [v*s (a-v a-s)
        ((b a-v) a-s)])))

(define-syntax (sdo stx)
  (syntax-case stx (<-)
    [(_ [dc <- rhs]) #'rhs]
    [(_ rhs) #'rhs]
    [(_ [name <- rhs] clause ...)
     #'(bind rhs (lambda (name) (sdo clause ...)))]
    [(_ rhs clause ...)
     #'(bind rhs (lambda (unused) (sdo clause ...)))]))

; Interprets the given expression, using the list of funs to resolve 
; appClications.
; taken from Assignment 3 by John Clements
(define (interp [expr : OWQQ4] 
                [env : Environment]) : (Store -> Result)
    (type-case OWQQ4 expr
      [numC (n) (lift (numV n))]
      [boolC (b) (lift (boolV b))]
      [binopC (s l r) 
        (bind 
          (interp l env)
          (lambda (lval) 
            (bind 
              (interp r env)
              (lambda (rval)
                (lift (binopC-to-NumV s lval rval))))))]
      ; [idC (id) (lookup id env)]
      ; [ifC (c t f) (local [(define condition (interp c env))
      ;                      (define then (interp t env))
      ;                      (define els (interp f env))]
      ;                (type-case Value condition
      ;                  [boolV (b) (if b then els)]
      ;                  [else (error 'interp "expected boolean")]))] 
      ; [lamC (params body) (lift (cloV params body env))]
      ; [appC (fn args) 
      ;   (type-case Value (interp fn env)
      ;     [cloV (params body env)
      ;       (local [(define (interp-again expr) (interp expr env))
      ;               (define arg-vals (map interp-again args))
      ;               (define new-env (add-to-env params arg-vals env))]
      ;         (interp body new-env))]
      ;     [else (error 'interp "expected function")])]
      [else (error 'interp "not implemented")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Test Cases without Mutation
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test ((interp (numC 3) empty-env) empty-store) 
      (v*s (numV 3) empty-store))
(test ((interp (numC 8) empty-env) empty-store)
      (v*s (numV 8) empty-store))
(test ((interp (boolC #t) empty-env) empty-store) 
      (v*s (boolV #t) empty-store))
(test ((interp (boolC #f) empty-env) empty-store) 
      (v*s (boolV #f) empty-store))
(test ((interp (binopC '+ (numC 3) (numC 3)) empty-env) empty-store) 
      (v*s (numV 6) empty-store))
(test ((interp (binopC '- (numC 3) (numC 3)) empty-env) empty-store)
      (v*s (numV 0) empty-store))
(test ((interp (binopC '* (numC 3) (numC 3)) empty-env) empty-store)
      (v*s (numV 9) empty-store))
(test ((interp (binopC '/ (numC 3) (numC 3)) empty-env) empty-store)
      (v*s (numV 1) empty-store))
; (test (interp (idC 'x)
;               (list (binding 'x (numV 3))
;                     (binding 'y (numV 4))))
;       (numV 3))
; (test (interp (ifC (boolC #t) (numC 4) (numC 5)) empty-env) (numV 4))
; (test (interp (ifC (boolC #f) (numC 4) (numC 5)) empty-env) (numV 5))
; (test/exn (interp (ifC (numC 3) (numC 4) (numC 5)) empty-env) 
;           "expected boolean")
; (test/exn (interp (idC 'x) empty-env) "unbound identifier")
; (test ((interp (lamC (list 'x 'y) (numC 3)) empty-env) empty-store)
      ; (v*s (cloV (list 'x 'y) (numC 3) (list)) empty-store))
; (test (interp (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
;                     (list (binopC '+ (numC 9) (numC 14)) (numC 98))) 
;               empty-env)
;       (numV 121))
; (test/exn (interp (appC (numC 3) empty) empty-env)
;           "expected function")

; Consumes a value and produces a string
; taken from Assignment 3 by John Clements
(define (serialize [value : Value]) : string
  (type-case Value value
    [numV (n) (to-string n)]
    [boolV (b) 
      (cond 
        [(equal? b #t) "true"]
        [else "false"])]
    [cloV (p b e) "#<procedure>"]
    [nullV () "null"]))

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")
(test (serialize (cloV (list 'x 'y) (binopC '+ (numC 3) (numC 4)) empty-env)) 
                 "#<procedure>")
(test (serialize (nullV)) "null")

; consumes an expression and parses and interprets it
; taken from Assignment 3 by John Clements
; (define (top-eval [s : s-expression]) : string
;   (serialize (interp (parse s) empty-env)))

; ; taken from Assignment 3 by John Clements
; (test (top-eval '{+ 12 4}) "16")
; (test (top-eval '{* 12 4}) "48")
; (test (top-eval '{- 12 4}) "8")
; (test (top-eval '{/ 12 4}) "3")
; (test (top-eval `true) "true")
; (test (top-eval `false) "false")
; (test (top-eval '{if true 3 4}) "3")
; (test (top-eval '{if true {+ 8 8} {+ 1 1}}) "16")
; (test (top-eval '{{func {z y} {+ z y}} {+ 9 14} 98}) "121")
; (test (top-eval '{with {z = {+ 9 14}}
;                        {y = 98}
;                        {+ z y}})
;       "121")





