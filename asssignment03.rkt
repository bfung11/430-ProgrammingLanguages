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
  [funcC (params : (listof symbol))
         (body : OWQQ3)]
  [binopC (op : symbol) ; operator
          (l : OWQQ3) 
          (r : OWQQ3)]
  [appC (fn : symbol) 
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
  [bind (name : symbol) (val : number)])
 
(define-type-alias Environment (listof Binding))
(define empty-env empty)
(define extend-env cons)

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

; Parses an expression.
; expected vs. actual
(define (parse [s : s-expression]) : OWQQ3
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? `SYMBOL s) (idC (s-exp->symbol s))]
      [(s-exp-match? `{if ANY ANY ANY} s) 
        (local [(define a-list (s-exp->list s))]
          (ifC (parse (second a-list)) 
               (parse (third a-list)) 
               (parse (fourth a-list))))]
      ; [(s-exp-match? `{func {ANY ANY ...} ANY} s)
      ;   (local [(define a-list (s-exp->list s))
      ;           (define params (second a-list))]
      ;     (funcC (map parse params)
      ;            (parse (second a-list))))]
      [(s-exp-match? '{SYMBOL ANY ...} s)
         (local [(define a-list (s-exp->list s))
                 (define first-sym (s-exp->symbol (first a-list)))]
          (cond [(some? (hash-ref binop-table first-sym))
                 (binopC (s-exp->symbol (first a-list)) 
                  (parse (second a-list)) (parse (third a-list)))]
                [else (appC first-sym (map parse (rest a-list)))]))]))

(test (parse '3) (numC 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse `x) (idC 'x))
(test (parse '{if 1 2 3}) (ifC (numC 1) (numC 2) (numC 3)))
(test (parse '{+ 3 3}) (binopC '+ (numC 3) (numC 3)))
(test (parse '{- 3 3}) (binopC '- (numC 3) (numC 3)))
(test (parse '{* 3 3}) (binopC '* (numC 3) (numC 3)))
(test (parse '{/ 3 3}) (binopC '/ (numC 3) (numC 3)))
(test (parse '{/ x 3}) (binopC '/ (idC 'x) (numC 3)))

; Parses a function definition by consuming an s-expression and produces a
; FundefC
; taken from Assignment 2 by John Clements
(define (parse-fundef [s : s-expression]) : FundefC
  (cond [(s-exp-match? '{func {SYMBOL SYMBOL ...} ANY} s)
          (local [(define fun-list (s-exp->list s))
                  (define sym-list (s-exp->list (second fun-list)))
                  (define fun-name (s-exp->symbol (first sym-list)))
                  (define args (rest sym-list))
                  (define body (third fun-list))]
                    (fundef fun-name (map s-exp->symbol args) (parse body)))]))

(test (parse-fundef '{func {none} {+ 4 5}}) 
      (fundef 'none (list ) (binopC '+ (numC 4) (numC 5))))
(test (parse-fundef '{func {pumpkin x} {+ 4 x}}) 
      (fundef 'pumpkin (list 'x) (binopC '+ (numC 4) (idC 'x))))
(test (parse-fundef '{func {lots x y} {+ 4 x}}) 
      (fundef 'lots (list 'x 'y) (binopC '+ (numC 4) (idC 'x))))
(test (parse-fundef (first (s-exp->list '{{func {f x y} {+ x y}}})))
      (fundef 'f (list 'x 'y) (binopC '+ (idC 'x) (idC 'y))))

; Parses a list of function definitions by consuming an s-expression and 
; produces a list of FundefC
(define (parse-prog [s : s-expression]) : (listof FundefC)
  (local [(define all-funs (s-exp->list s))]
    (map parse-fundef all-funs)))

(test (parse-prog '{{func {f x y} {+ x y}}
                    {func {main} {f 1 2}}})
      (list (fundef 'f (list 'x 'y) (binopC '+ (idC 'x) (idC 'y)))
            (fundef 'main (list ) (appC 'f (list (numC 1) (numC 2))))))
(test (parse-prog '{{func {f} 5}
                    {func {main} {+ {f} {f}}}})
      (list (fundef 'f (list ) (numC 5))
            (fundef 'main (list ) (binopC '+ (appC 'f (list )) (appC 'f (list ))))))

(define (lookup [for : symbol] [env : Environment]) : number
  (cond 
    [(empty? env) (error 'lookup "unbound identifier")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(test (lookup 'x 
              (list (bind 'x 3)
                    (bind 'y 4)))
      3)
(test (lookup 'y
              (list (bind 'x 3)
                    (bind 'y 4)))
      4)
; (test (interp (binopC '+ (numC 10) (appC 'const5 (numC 10)))
;               empty-env
;               (list (fdC 'const5 '_ (numC 5))))
;       15)
 
; (test (interp (binopC '+ (numC 10) (appC 'double (binopC '+ (numC 1) (numC 2))))
;               empty-env
;               (list (fdC 'double 'x (binopC '+ (idC 'x) (idC 'x)))))
;       16)
 
; (test (interp (binopC '+ (numC 10) (appC 'quadruple (binopC '+ (numC 1) (numC 2))))
;               empty-env
;               (list (fdC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
;                     (fdC 'double 'x (binopC '+ (idC 'x) (idC 'x)))))
;       22)

(define (binopC-to-NumV [op : symbol] [left : Value] [right : Value]) : Value
  (numV ((some-v (hash-ref binop-table op)) 
         (numV-num left)
         (numV-num right))))

(test (binopC-to-NumV '+ (numV 4) (numV 4)) (numV 8))
(test (binopC-to-NumV '* (numV 4) (numV 4)) (numV 16))
(test (binopC-to-NumV '- (numV 4) (numV 4)) (numV 0))
(test (binopC-to-NumV '/ (numV 4) (numV 4)) (numV 1))

; Interprets the given expression, using the list of funs to resolve 
; appClications.
; taken from Assignment 2 by John Clements
(define (interp [expr : OWQQ3] 
                [env : Environment]) : Value
  (type-case OWQQ3 expr
    [numC (n) (numV n)]
    [boolC (b) (boolV b)]
    [binopC (s l r) (binopC-to-NumV s (interp l env) (interp r env))]
    [idC (id) (numV (lookup id env))]
    [ifC (c t f) (local [(define condition (interp c env))
                         (define then (interp t env))
                         (define els (interp f env))]
                   (type-case Value condition
                     [boolV (b) (if b then els)]
                     [else (error 'interp "expected boolean")]))] 
    [appC (fn args) (error 'interp "appC not implemented")]))
    ; [appC (fn args)
    ;   (type-case FundefC (lookup fn funs)
    ;     [fundef (name params body) (interp body funs env)])]

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
              (list (bind 'x 3)
                    (bind 'y 4)))
      (numV 3))
(test (interp (ifC (boolC #t) (numC 4) (numC 5)) empty-env) (numV 4))
(test (interp (ifC (boolC #f) (numC 4) (numC 5)) empty-env) (numV 5))
; question: is 3 a valid number
(test/exn (interp (ifC (numC 3) (numC 4) (numC 5)) empty-env) 
          "expected boolean")
(test/exn (interp (idC 'x) empty-env) "unbound identifier")
; (test (interp (appC 'f (list (numC 3) (numC 4))) empty-env)
;       (numV 5))

; consumes an expression and parses and interprets it
; taken from Assignment 2 by John Clements
; (define (top-eval [fun-sexps : s-expression])  : number
;   (interp-fns (parse-prog fun-sexps)))
(define (top-eval [s : s-expression]) : string
  (serialize (interp (parse s) empty-env)))

(test (top-eval '(+ 12 4)) "16")
(test (top-eval '(* 12 4)) "48")
(test (top-eval '(- 12 4)) "8")
(test (top-eval '(/ 12 4)) "3")
(test (top-eval `true) "true")
(test (top-eval `false) "false")





