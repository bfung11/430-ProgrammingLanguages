#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ3
  [num (n : number)]
  [boolC (b : boolean)]
  [ifleq (condition : OWQQ3) 
         (if-true : OWQQ3) 
         (if-false : OWQQ3)]
  [binop (op : symbol) 
         (l : OWQQ3) 
         (r : OWQQ3)]
  [idC (id : symbol)]
  [app (fn : symbol) 
       (args : (listof OWQQ3))])

(define-type FundefC
  [fundef (name : symbol) 
          (params : (listof symbol)) 
          (body : OWQQ3)])

(define-type Value
  [numV (num : number)]
  [boolV (bool : boolean)])

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
        [else "false"])]))

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")

; Parses an expression.
(define (parse [s : s-expression]) : OWQQ3
   (cond 
      [(s-exp-number? s) (num (s-exp->number s))]
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
                 (binop (s-exp->symbol (first a-list)) 
                  (parse (second a-list)) (parse (third a-list)))]
                [else (app first-sym (map parse (rest a-list)))]))]))

(test (parse '3) (num 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse '{ifleq0 2 0 5}) (ifleq (num 2) (num 0) (num 5)))
(test (parse '{ifleq0 x 0 5}) (ifleq (idC 'x) (num 0) (num 5)))
(test (parse '{+ 3 3}) (binop '+ (num 3) (num 3)))
(test (parse '{- 3 3}) (binop '- (num 3) (num 3)))
(test (parse '{* 3 3}) (binop '* (num 3) (num 3)))
(test (parse '{/ 3 3}) (binop '/ (num 3) (num 3)))
(test (parse '{/ x 3}) (binop '/ (idC 'x) (num 3)))
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
      (fundef 'none (list ) (binop '+ (num 4) (num 5))))
(test (parse-fundef '{func {pumpkin x} {+ 4 x}}) 
      (fundef 'pumpkin (list 'x) (binop '+ (num 4) (idC 'x))))
(test (parse-fundef '{func {lots x y} {+ 4 x}}) 
      (fundef 'lots (list 'x 'y) (binop '+ (num 4) (idC 'x))))
(test (parse-fundef (first (s-exp->list '{{func {f x y} {+ x y}}})))
      (fundef 'f (list 'x 'y) (binop '+ (idC 'x) (idC 'y))))

; Parses a list of function definitions by consuming an s-expression and 
; produces a list of FundefC
(define (parse-prog [s : s-expression]) : (listof FundefC)
  (local [(define all-funs (s-exp->list s))]
    (map parse-fundef all-funs)))

(test (parse-prog '{{func {f x y} {+ x y}}
                    {func {main} {f 1 2}}})
      (list (fundef 'f (list 'x 'y) (binop '+ (idC 'x) (idC 'y)))
            (fundef 'main (list ) (app 'f (list (num 1) (num 2))))))
(test (parse-prog '{{func {f} 5}
                    {func {main} {+ {f} {f}}}})
      (list (fundef 'f (list ) (num 5))
            (fundef 'main (list ) (binop '+ (app 'f (list )) (app 'f (list ))))))

; Look up the function in the list of functions in funs
(define (lookup [a-name : symbol] [funs : (listof FundefC)]) : FundefC
  (cond [(empty? funs) (error 'lookup "function list is empty")]
        [else (cond [(equal? a-name (fundef-name (first funs))) (first funs)]
                    [else (lookup a-name (rest funs))])]))

(test/exn (lookup 'x
                  (list (fundef 'f (list ) (num 5))
                        (fundef 'main (list ) 
                                (binop '+ (app 'f (list )) (app 'f (list ))))))
          "function list is empty")
(test (lookup 'f
              (list (fundef 'f (list ) (num 5))
                    (fundef 'main (list ) 
                         (binop '+ (app 'f (list )) (app 'f (list ))))))
      (fundef 'f (list ) (num 5)))
(test (lookup 'main (list (fundef 'f (list ) (num 5))
                          (fundef 'main (list ) 
                                 (binop '+ (app 'f (list )) (app 'f (list ))))))
      (fundef 'main (list ) (binop '+ (app 'f (list )) (app 'f (list )))))
(test (lookup 'main (list (fundef 'add (list ) (binop '+ (num 2) (num 3)))
                        (fundef 'main (list ) (app 'f (list )))))
      (fundef 'main (list ) (app 'f (list ))))

; Interprets the given expression, using the list of funs to resolve 
; applications.
; taken from Assignment 2 by John Clements
(define (interp [expr : OWQQ3] [funs : (listof FundefC)]) : number
  (type-case OWQQ3 expr
    [num (n) n]
    [ifleq (c t f) 
      (cond [(= (interp c funs) 0) (interp t funs)]
            [else (interp f funs)])]
    [binop (s l r) ((some-v (hash-ref binop-table s)) 
                    (interp l funs) (interp r funs))]
    [idC (id) (error 'interp "unbound identifier")]
    [app (fn args)
      (type-case FundefC (lookup fn funs)
        [fundef (name params body) (interp body funs)])]
    [else -1]))

(test (interp (ifleq (num 2) (num 0) (num 5)) (list )) 5)
(test (interp (ifleq (num 0) (num 8) (num 3)) (list )) 8)
(test (interp (binop '+ (num 3) (num 3)) (list )) 6)
(test (interp (binop '- (num 3) (num 3)) (list )) 0)
(test (interp (binop '* (num 3) (num 3)) (list )) 9)
(test (interp (binop '/ (num 3) (num 3)) (list )) 1)
(test/exn (interp (idC 'x) (list )) "unbound identifier")
(test (interp (app 'f (list (num 3) (num 4))) 
              (list (fundef 'f (list 'x 'y) (binop '+ (num 2) (num 3)))))
      5)

; Interprets the function named main from the fundefs.
; taken from Assignment 2 by John Clements
(define (interp-fns [funs : (listof FundefC)]) : number
    (type-case FundefC (lookup 'main funs)
      (fundef (name args body) (interp body funs))))

; testcase - no idCs
; testcase - idCs but not used
; testcase - use idCs
(test (interp-fns (list (fundef 'add (list ) (binop '+ (num 2) (num 3)))
                        (fundef 'main (list ) (app 'add (list )))))
      5)
(test (interp-fns (list (fundef 'add (list 'x 'y) (binop '+ (num 2) (num 3)))
                        (fundef 'main (list ) (app 'add (list (num 10) (num 20))))))
      5)

; wrong code - required to save submission
; (test (interp-fns (list (fundef 'f (list 'x 'y) (binop '+ (idC 'x) (idC 'y)))
;                         (fundef 'main (list ) (app 'f (list (num 1) (num 2))))))
;       3)
; replaces all occurrences of a idC with a number
; (define (subst [s : s-expression]) : s-expression
;   )