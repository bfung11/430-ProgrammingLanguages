#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)

(define-type OWQQ2
  [num (n : number)]
  [ifleq (condition : OWQQ2) 
         (if-true : OWQQ2) 
         (if-false : OWQQ2)]
  [binop (op : symbol) 
         (l : OWQQ2) 
         (r : OWQQ2)]
  [var (id : symbol)]
  [app (fn : symbol) 
       (args : (listof OWQQ2))])

(define-type FundefC
  [fundef (name : symbol) 
          (params : (listof symbol)) 
          (body : OWQQ2)])

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))

; consumes an expression and parses and interprets it
; taken from Assignment 2 by John Clements
; (define (top-eval [fun-sexps : s-expression])  : number
;   (interp-fns (parse-prog fun-sexps)))

; wrong code - required to save submission
(define (top-eval [fun-sexps : s-expression])  : number
  10)

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

; Parses an expression.
(define (parse [s : s-expression]) : OWQQ2
   (cond 
      [(s-exp-number? s) (num (s-exp->number s))]
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
                [else (app first-sym (map parse (rest a-list)))]))]
      [(s-exp-match? `SYMBOL s) (var (s-exp->symbol s))]))

(test (parse '3) (num 3))
(test (parse '{ifleq0 2 0 5}) (ifleq (num 2) (num 0) (num 5)))
(test (parse '{ifleq0 x 0 5}) (ifleq (var 'x) (num 0) (num 5)))
(test (parse '{+ 3 3}) (binop '+ (num 3) (num 3)))
(test (parse '{- 3 3}) (binop '- (num 3) (num 3)))
(test (parse '{* 3 3}) (binop '* (num 3) (num 3)))
(test (parse '{/ 3 3}) (binop '/ (num 3) (num 3)))
(test (parse '{/ x 3}) (binop '/ (var 'x) (num 3)))
(test (parse `x) (var 'x))

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
      (fundef 'pumpkin (list 'x) (binop '+ (num 4) (var 'x))))
(test (parse-fundef '{func {lots x y} {+ 4 x}}) 
      (fundef 'lots (list 'x 'y) (binop '+ (num 4) (var 'x))))
(test (parse-fundef (first (s-exp->list '{{func {f x y} {+ x y}}})))
      (fundef 'f (list 'x 'y) (binop '+ (var 'x) (var 'y))))

; Parses a list of function definitions by consuming an s-expression and 
; produces a list of FundefC
(define (parse-prog [s : s-expression]) : (listof FundefC)
  (local [(define all-funs (s-exp->list s))]
    (map parse-fundef all-funs)))

(test (parse-prog '{{func {f x y} {+ x y}}
                    {func {main} {f 1 2}}})
      (list (fundef 'f (list 'x 'y) (binop '+ (var 'x) (var 'y)))
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
(define (interp [expr : OWQQ2] [funs : (listof FundefC)]) : number
  (type-case OWQQ2 expr
    [num (n) n]
    [ifleq (c t f) 
      (cond [(= (interp c funs) 0) (interp t funs)]
            [else (interp f funs)])]
    [binop (s l r) ((some-v (hash-ref binop-table s)) 
                    (interp l funs) (interp r funs))]
    [var (id) (error 'interp "unbound identifier")]
    [app (fn args)
      (type-case FundefC (lookup fn funs)
        [fundef (name params body) (interp body funs)])]))

(test (interp (ifleq (num 2) (num 0) (num 5)) (list )) 5)
(test (interp (ifleq (num 0) (num 8) (num 3)) (list )) 8)
(test (interp (binop '+ (num 3) (num 3)) (list )) 6)
(test (interp (binop '- (num 3) (num 3)) (list )) 0)
(test (interp (binop '* (num 3) (num 3)) (list )) 9)
(test (interp (binop '/ (num 3) (num 3)) (list )) 1)
(test/exn (interp (var 'x) (list )) "unbound identifier")
(test (interp (app 'f (list (num 3) (num 4))) 
              (list (fundef 'f (list 'x 'y) (binop '+ (num 2) (num 3)))))
      5)

; Interprets the function named main from the fundefs.
; taken from Assignment 2 by John Clements
(define (interp-fns [funs : (listof FundefC)]) : number
    (type-case FundefC (lookup 'main funs)
      (fundef (name args body) (interp body funs))))

; testcase - no vars
; testcase - vars but not used
; testcase - use vars
(test (interp-fns (list (fundef 'add (list ) (binop '+ (num 2) (num 3)))
                        (fundef 'main (list ) (app 'add (list )))))
      5)
(test (interp-fns (list (fundef 'add (list 'x 'y) (binop '+ (num 2) (num 3)))
                        (fundef 'main (list ) (app 'add (list (num 10) (num 20))))))
      5)

; wrong code - required to save submission
; (test (interp-fns (list (fundef 'f (list 'x 'y) (binop '+ (var 'x) (var 'y)))
;                         (fundef 'main (list ) (app 'f (list (num 1) (num 2))))))
;       3)
; replaces all occurrences of a var with a number
; (define (subst [s : s-expression]) : s-expression
;   )