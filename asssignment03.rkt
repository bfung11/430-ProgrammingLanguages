#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ3
  [numC (n : number)]
  [boolC (b : boolean)]
  [ifleq (condition : OWQQ3) 
         (if-true : OWQQ3) 
         (if-false : OWQQ3)]
  [binopC (op : symbol) 
         (l : OWQQ3) 
         (r : OWQQ3)]
  [idC (id : symbol)]
  [appC (fn : symbol) 
       (args : (listof OWQQ3))])

(define-type-alias Environment (hashof symbol Value))

(define-type FundefC
  [fundef (name : symbol) 
          (params : (listof symbol)) 
          (body : OWQQ3)])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)]
  [closureV (params : (listof symbol))
            (body : OWQQ3)
            (env : Environment)])

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))
 

(define env (hash (list)))

; consumes an expression and parses and interprets it
; taken from Assignment 2 by John Clements
; (define (top-eval [fun-sexps : s-expression])  : number
;   (interp-fns (parse-prog fun-sexps)))

; (define (top-eval [s : s-expression]) : string
;   (serialize (interp (parse s) empty-env)))
(define (top-eval [s : s-expression]) : string
  "implement me please :)")

; bad tests - required test case to save submission
; (test (top-eval '(+ 3 3)) 6)
; example test cases
; (test (interp-fns
;        (parse-prog '{{func {f x y} {+ x y}}
;                      {func {main} {f 1 2}}}))
;       3)
;  (test (interp-fns
;         (parse-prog '{{func {f} 5}
;                       {func {main} {+ {f} {f}}}}))
;        10)
;  (test/exn (interp-fns
;             (parse-prog '{{func {f x y} {+ x y}}
;                           {func {main} {f 1}}}))
;            "wrong arity")

(define (serialize [value : Value]) : string
  (type-case Value value
    [numV (n) (to-string n)]
    [boolV (b) 
      (cond 
        [(equal? b #t) "true"]
        [else "false"])]
    [closureV (p b e) "#<procedure>"]))

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")
(test (serialize (closureV (list 'x 'y) (binopC '+ (numC 3) (numC 4)) env)) 
                 "#<procedure>")

; Parses an expression.
(define (parse [s : s-expression]) : OWQQ3
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? `SYMBOL s) (idC (s-exp->symbol s))]
      [(s-exp-match? '{ifleq0 ANY ANY ANY} s)
         (local [(define a-list (s-exp->list s))]
          (ifleq (parse (second a-list)) 
                 (parse (third a-list)) 
                 (parse (fourth a-list))))]
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
(test (parse '{ifleq0 2 0 5}) (ifleq (numC 2) (numC 0) (numC 5)))
(test (parse '{ifleq0 x 0 5}) (ifleq (idC 'x) (numC 0) (numC 5)))
(test (parse '{+ 3 3}) (binopC '+ (numC 3) (numC 3)))
(test (parse '{- 3 3}) (binopC '- (numC 3) (numC 3)))
(test (parse '{* 3 3}) (binopC '* (numC 3) (numC 3)))
(test (parse '{/ 3 3}) (binopC '/ (numC 3) (numC 3)))
(test (parse '{/ x 3}) (binopC '/ (idC 'x) (numC 3)))
(test (parse `x) (idC 'x))

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

; Look up the function in the list of functions in funs
(define (lookup [a-name : symbol] [funs : (listof FundefC)]) : FundefC
  (cond [(empty? funs) (error 'lookup "function list is empty")]
        [else (cond [(equal? a-name (fundef-name (first funs))) (first funs)]
                    [else (lookup a-name (rest funs))])]))

(test/exn (lookup 'x
                  (list (fundef 'f (list ) (numC 5))
                        (fundef 'main (list ) 
                                (binopC '+ (appC 'f (list )) (appC 'f (list ))))))
          "function list is empty")
(test (lookup 'f
              (list (fundef 'f (list ) (numC 5))
                    (fundef 'main (list ) 
                         (binopC '+ (appC 'f (list )) (appC 'f (list ))))))
      (fundef 'f (list ) (numC 5)))
(test (lookup 'main (list (fundef 'f (list ) (numC 5))
                          (fundef 'main (list ) 
                                 (binopC '+ (appC 'f (list )) (appC 'f (list ))))))
      (fundef 'main (list ) (binopC '+ (appC 'f (list )) (appC 'f (list )))))
(test (lookup 'main (list (fundef 'add (list ) (binopC '+ (numC 2) (numC 3)))
                        (fundef 'main (list ) (appC 'f (list )))))
      (fundef 'main (list ) (appC 'f (list ))))

; Interprets the given expression, using the list of funs to resolve 
; appClications.
; taken from Assignment 2 by John Clements
(define (interp [expr : OWQQ3] 
                [funs : (listof FundefC)] 
                [env : Environment]) : number
  (type-case OWQQ3 expr
    [numC (n) n]
    [ifleq (c t f) 
      (cond [(= (interp c funs env) 0) (interp t funs env)]
            [else (interp f funs env)])]
    [binopC (s l r) ((some-v (hash-ref binop-table s)) 
                    (interp l funs env) (interp r funs env))]
    [idC (id) (error 'interp "unbound identifier")]
    [appC (fn args)
      (type-case FundefC (lookup fn funs)
        [fundef (name params body) (interp body funs env)])]
    [else -1]))

(test (interp (ifleq (numC 2) (numC 0) (numC 5)) (list ) env) 5)
(test (interp (ifleq (numC 0) (numC 8) (numC 3)) (list ) env) 8)
(test (interp (binopC '+ (numC 3) (numC 3)) (list ) env) 6)
(test (interp (binopC '- (numC 3) (numC 3)) (list ) env) 0)
(test (interp (binopC '* (numC 3) (numC 3)) (list ) env) 9)
(test (interp (binopC '/ (numC 3) (numC 3)) (list ) env) 1)
(test/exn (interp (idC 'x) (list ) env) "unbound identifier")
(test (interp (appC 'f (list (numC 3) (numC 4))) 
              (list (fundef 'f (list 'x 'y) (binopC '+ (numC 2) (numC 3)))) env)
      5)

; Interprets the function named main from the fundefs.
; taken from Assignment 2 by John Clements
(define (interp-fns [funs : (listof FundefC)]) : number
    (type-case FundefC (lookup 'main funs)
      (fundef (name args body) (interp body funs env))))

; testcase - no idCs
; testcase - idCs but not used
; testcase - use idCs
(test (interp-fns (list (fundef 'add (list ) (binopC '+ (numC 2) (numC 3)))
                        (fundef 'main (list ) (appC 'add (list )))))
      5)
(test (interp-fns (list (fundef 'add (list 'x 'y) (binopC '+ (numC 2) (numC 3)))
                        (fundef 'main (list ) (appC 'add (list (numC 10) (numC 20))))))
      5)

; wrong code - required to save submission
; (test (interp-fns (list (fundef 'f (list 'x 'y) (binop '+ (idC 'x) (idC 'y)))
;                         (fundef 'main (list ) (appC 'f (list (num 1) (num 2))))))
;       3)
; replaces all occurrences of a idC with a number
; (define (subst [s : s-expression]) : s-expression
;   )