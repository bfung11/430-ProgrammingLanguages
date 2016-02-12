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
  [array-refC (id : OWQQ4)
              (index : OWQQ4)]
  [array-setC (id : OWQQ4)
              (index : OWQQ4)
              (new-value : OWQQ4)]
  [setC (id : symbol)
        (new-value : OWQQ4)]
  [beginC (functions : (listof OWQQ4))]
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
  [arrayV (location : Location)
          (length : number)]
  [nullV])

(define binop-table
  (hash (list (values '+ +)
              (values '- -)
              (values '* *)
              (values '/ /))))

; (define (is-equal? [left : 'a] [right : 'a]) : Value
;   (equal? left right))

(define id-keywords (list 'if 'true 'false 'fn 'with  'array '<- '= 'begin))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Environment Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-type-alias Environment (hashof symbol Location))
(define empty-env (hash empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Store Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type-alias Location number)

(define-type-alias Store (hashof Location Value))
(define empty-store (hash empty))
(define store-loc -1) ; start at -1 because after add, starts at index 0

(define-type Result
  [v*s (v : Value) (s : Store)])

;;;;;;;;;;;;;;;;;;;;
;
; Parser
;
;;;;;;;;;;;;;;;;;;;;

(define empty-array 1)

(define (create-array [num : number]
                      [elem : 'a]) : (listof 'a)
  (cond [(= num 0) empty]
        [else (cons elem (create-array (- num 1) elem))]))

(test (create-array 0 200) empty)
(test (create-array 4 1)
      (list 1 1 1 1))

; takes a symbol and checks whether or not the id can be used
(define (is-id-legal? [sym : symbol]) : boolean
  (and (none? (hash-ref binop-table sym))
       (not (member sym id-keywords))))

(test (is-id-legal? 'if) #f)
(test (is-id-legal? 'a) #t)

; takes a symbol list and checks whether all symbols are unique
(define (is-symbol-unique? [sym-list : (listof symbol)]) : boolean
  (cond 
    [(empty? sym-list) #t]
    [else (and (not (member (first sym-list) (rest sym-list)))
               (is-symbol-unique? (rest sym-list)))]))

(test (is-symbol-unique? (list 'a 'b 'a)) #f)
(test (is-symbol-unique? (list 'a 'b 'c)) #t)

; Parses an expression.
; expected vs. actual
; taken from Assignment 3 by John Clements
; bug? array and new-array -> fewer than 1 cell
(define (parse [s : s-expression]) : OWQQ4
   (cond 
      [(s-exp-number? s) (numC (s-exp->number s))]
      [(s-exp-match? `true s) (boolC #t)]
      [(s-exp-match? `false s) (boolC #f)]
      [(s-exp-match? `SYMBOL s) 
        (cond [(is-id-legal? (s-exp->symbol s)) (idC (s-exp->symbol s))]
              [else (error 'parse "not a valid symbol")])]
      [(s-exp-match? '{new-array ANY ANY} s)
        (local [(define a-list (s-exp->list s))
                (define num-cells (s-exp->number (second a-list)))]
          (cond 
            [(< num-cells 1) 
             (error 'parse "array must contain at least one cell")]
            [else (arrayC (map parse (create-array num-cells 
                                                   (third a-list))))]))]
      [(s-exp-match? '{array ANY ANY ...} s)
        (local [(define a-list (s-exp->list s))]
          (arrayC (map parse (rest a-list))))]
      [(s-exp-match? '{ref ANY[ANY]} s)
        (local [(define a-list (s-exp->list s))]
          (array-refC (parse (second a-list)) 
                      (parse (first (s-exp->list (third a-list))))))]
      [(s-exp-match? '{ANY[ANY] <- ANY} s)
        (local [(define a-list (s-exp->list s))]
          (array-setC (parse (first a-list))
                      (parse (first (s-exp->list (second a-list))))
                      (parse (fourth a-list))))]
      [(s-exp-match? '{SYMBOL <- ANY} s) 
        (local [(define a-list (s-exp->list s))]
          (setC (s-exp->symbol (first a-list)) 
                (parse (third a-list))))]
      [(s-exp-match? '{begin ANY ANY ...} s) 
        (local [(define a-list (s-exp->list s))]
          (beginC (map parse (rest a-list))))]
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
          (cond 
            [(is-symbol-unique? params) (lamC params (parse (third a-list)))]
            [else (error 'parse "params not unique")]))]
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

; (equal? (length (s-exp->list '{array})) 1)

; taken from Assignment 3 by John Clements
; base types test cases
(test (parse '3) (numC 3))
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))
(test (parse `x) (idC 'x))
(test/exn (parse '{+ if with})
          "not a valid symbol")

; array test cases
(test/exn (parse '{array})
          "not a valid symbol")
(test (parse '{array 3 false {+ 3 2} x})
      (arrayC (list (numC 3) 
                    (boolC #f) 
                    (binopC '+ (numC 3) (numC 2))
                    (idC 'x))))
(test (parse '{new-array 3 true})
      (arrayC (list (boolC #t)
                    (boolC #t)
                    (boolC #t))))
(test/exn (parse '{new-array 0 200})
          "array must contain at least one cell")
(test (parse '{ref p [3]})
      (array-refC (idC 'p) (numC 3)))
(test (parse '{ref p [x]})
      (array-refC (idC 'p) (idC 'x)))
(test (parse '{ref p [{+ 3 2}]})
      (array-refC (idC 'p) (binopC '+ (numC 3) (numC 2))))
(test (parse '{p [15] <- 3})
      (array-setC (idC 'p) (numC 15) (numC 3)))
(test (parse '{p [x] <- x})
      (array-setC (idC 'p) (idC 'x) (idC 'x)))
(test (parse '{p [{+ 3 x}] <- {- x 5}})
      (array-setC (idC 'p) 
                  (binopC '+ (numC 3) (idC 'x)) 
                  (binopC '- (idC 'x) (numC 5))))
(test (parse '{p <- 3})
      (setC 'p (numC 3)))
(test (parse '{p <- x})
      (setC 'p (idC 'x)))
(test (parse '{p <- {+ 3 y}})
      (setC 'p (binopC '+ (numC 3) (idC 'y))))
(test (parse '{begin {f x} 9})
      (beginC (list (appC (idC 'f) (list (idC 'x))) 
                    (numC 9))))

; all other
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
(test/exn (parse '{func {x x} 3})
          "params not unique")

(test (parse '{+ 3 3}) (binopC '+ (numC 3) (numC 3)))
(test (parse '{- 3 3}) (binopC '- (numC 3) (numC 3)))
(test (parse '{* 3 3}) (binopC '* (numC 3) (numC 3)))
(test (parse '{/ 3 3}) (binopC '/ (numC 3) (numC 3)))
(test (parse '{/ x 3}) (binopC '/ (idC 'x) (numC 3)))
(test/exn (parse '{+ + +}) "not a valid symbol")
(test (parse '{f 3 4}) (appC (idC 'f) (list (numC 3) (numC 4))))
(test (parse '{with {z = {+ 9 14}}
                    {y = 98}
                    {+ z y}})
      (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
            (list (binopC '+ (numC 9) (numC 14)) (numC 98))))

; consumes a symbol and an environment and returns the number associated with 
; the symbol
; taken from 
; Programming Languages: Application and Interpretation, 
; by Shriram Krishnamurthi, second edition.
; (define (lookup-evn [for : symbol] [env : Environment]) : Value
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
(define (do-binop [op : symbol] [left : Value] [right : Value]) : Value
  (numV ((some-v (hash-ref binop-table op)) 
         (numV-num left)
         (numV-num right))))

(test (do-binop '+ (numV 4) (numV 4)) (numV 8))
(test (do-binop '* (numV 4) (numV 4)) (numV 16))
(test (do-binop '- (numV 4) (numV 4)) (numV 0))
(test (do-binop '/ (numV 4) (numV 4)) (numV 1))

; interp before adding to env?
; function meant to add bindings to environment
; consumes a list of symbols, a list of Values and an environment and produces
; a list of Bindings
(define (add-to-env [params : (listof symbol)] 
                    [args : (listof Location)]
                    [env : Environment]) : Environment
  (cond 
    [(and (empty? params) (empty? args)) env]
    [else (add-to-env (rest params) 
          (rest args)
          (hash-set env (first params) (first args)))]))

(test (add-to-env (list 'x 'y 'z)
                  (list 3 5 7)
                  empty-env)
      (hash (list (values 'x 3)
                  (values 'y 5)
                  (values 'z 7))))

; alpha-computation = (Store -> (alpha * Store))
; (Value -> ((listof Sbind) -> Result))
; debugging - expected v. actual

;;;;;;;;;;;;;;;;;;;;;;;
;
; Monad Definitions
;
;;;;;;;;;;;;;;;;;;;;;;;

; when returning elements, just think of it as 
; using the do to return the type as normal
; and add a computation to it, so it knows what to do when a store is added

; give me a store and I will complete the rest
(define-type-alias (Computation 'a) (Store -> Result))

(define (lift [v : 'a])  : (Computation 'a)
  (lambda ([sto : Store]) (v*s v sto)))

(define (bind [a : (Computation 'a)]
              [b : ('a -> (Computation 'b))]) : (Computation 'b)
  (lambda ([sto : Store])
    (type-case Result (a sto)
      [v*s (a-v a-s)
        ((b a-v) a-s)])))

(define-syntax (do stx)
  (syntax-case stx (<-)
    [(_ [dc <- rhs]) #'rhs]
    [(_ rhs) #'rhs]
    [(_ [name <- rhs] clause ...)
     #'(bind rhs (lambda (name) (do clause ...)))]
    [(_ rhs clause ...)
     #'(bind rhs (lambda (unused) (do clause ...)))]))

;;;;;;;;;;;;;;;;;;;;
;
; Interpreter
;
;;;;;;;;;;;;;;;;;;;;

(define test-env (hash (list (values 'a 0) 
                             (values 'b 4)
                             (values 'x 10)
                             (values 'y 11))))
(define test-sto (hash (list (values 0 (arrayV 1 3))
                             (values 1 (numV 100))
                             (values 2 (numV 110))
                             (values 3 (numV 120))
                             (values 4 (arrayV 5 4))
                             (values 5 (numV 140))
                             (values 6 (numV 150))
                             (values 7 (boolV #t))
                             (values 8 (boolV #f))
                             (values 9 (numV 100))
                             (values 10 (numV 200))
                             (values 11 (numV 50)))))

(define (add-to-store [elements : (listof Value)]
                      [store : Store]) : Store
  (cond 
    [(empty? elements) store]
    [else (begin (set! store-loc (+ 1 store-loc))
                 (add-to-store (rest elements)
                               (hash-set store
                                         store-loc
                                         (first elements))))]))

(test (add-to-store empty empty-store) empty-store)
(test (add-to-store (list (numV 9) (numV 10) (numV 11)) empty-store)
      (hash (list (values 0 (numV 9))
                  (values 1 (numV 10))
                  (values 2 (numV 11)))))

(define (lookup-store [loc : Location]) : (Computation Value)
  (lambda ([store : Store])
    (type-case (optionof Value) (hash-ref store loc)
      [none () (error 'lookup-store (to-string loc))]
      [some (val) (v*s val store)])))

(test (v*s-v ((lookup-store 0) test-sto))
      (v*s-v (v*s (arrayV 1 3) empty-store)))
(test (v*s-v ((lookup-store 1) test-sto))
      (v*s-v (v*s (numV 100) empty-store)))
; (test/exn ((lookup-store 1000) test-sto)
;           "not in store")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Interpreter Helper Functions
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-array-index [id : Value]
                         [index : Value]
                         [env : Environment]) : (Computation Value)
  (do 
    (type-case Value id
      [arrayV (arr-start len)
        (do 
          (type-case Value index
            [numV (shift) 
              (cond 
                [(and (>= shift 0)
                      (< shift len))
                  (lift (do-binop '+ (numV arr-start) (numV shift)))]
                [else (error 'get-array-index "index out of bounds")])]
            [else (error 'get-array-index "expected index")]))]
      [else (error 'get-array-index "expected array")])))

(test (v*s-v ((get-array-index (arrayV 1 3) (numV 1) test-env) test-sto))
      (v*s-v (v*s (numV 2) test-sto)))
(test/exn (v*s-v ((get-array-index (boolV #t) (numV 2) test-env) test-sto))
          "expected array")
(test/exn (v*s-v ((get-array-index (arrayV 1 3) (boolV #f) test-env) test-sto))
          "expected index")
(test/exn (v*s-v ((get-array-index (arrayV 1 3) (numV 100) test-env) test-sto))
          "index out of bounds")

; (define (set-array [id : Value]
;                    [index : Value]
;                    [new-value : Value]
;                    [env : Environment]) : (Computation Value)
;   (type-case (get-array-index id index env)
; )

; Interprets the given expression, using the list of funs to resolve 
; appClications.
; taken from Assignment 3 by John Clements
(define (interp [expr : OWQQ4] 
                [env : Environment]) : (Computation Value)
    (type-case OWQQ4 expr
      [numC (n) (lift (numV n))]
      [boolC (b) (lift (boolV b))]
      [binopC (s l r) 
        (do [lval <- (interp l env)]
            [rval <- (interp r env)]
            (lift (do-binop s lval rval)))]
      [idC (id) 
        (type-case (optionof Location) (hash-ref env id)
            [none () (error 'interp "not in environment")]
            [some (loc) (lookup-store loc)])]
      [arrayC (elems) 
        (interp (first elems) env)]
      ; array
      [array-refC (id index) 
        (do [arr-start <- (interp id env)]
            [shift <- (interp index env)]
            [loc <- (get-array-index arr-start shift env)]
          (type-case Value loc
            [numV (n) (lookup-store n)]
            [else (error 'interp "not a location")]))]
      ; [array-setC (id index val)
      ;   (do [arr-start <- (interp id env)]
      ;       [shift <- (interp index env)]
      ;       [new-val <- (interp val env)]
      ;       ())]
      [ifC (c t f) 
        (do [cval <- (interp c env)]
            [tval <- (interp t env)]
            [fval <- (interp f env)]
              (type-case Value cval
                [boolV (b) (if b (interp t env) (interp f env))]
                [else (error 'interp "expected boolean")]))]
      [lamC (params body) (lift (cloV params body env))]
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
(test (v*s-v ((interp (idC 'x) test-env) test-sto))
      (v*s-v (v*s (numV 200) empty-store)))
(test (v*s-v ((interp (idC 'a) test-env) test-sto))
      (v*s-v (v*s (arrayV 1 3) empty-store)))
(test/exn (interp (idC 'z) test-env)
          "not in environment")
(test (v*s-v ((interp (ifC (boolC #t) (numC 4) (numC 5)) test-env) test-sto))
      (v*s-v (v*s (numV 4) empty-store)))
(test (v*s-v ((interp (ifC (boolC #f) (numC 4) (numC 5)) test-env) test-sto))
      (v*s-v (v*s (numV 5) empty-store)))
(test/exn (v*s-v ((interp (ifC (numC 5) (numC 4) (numC 5)) test-env) test-sto))
          "expected boolean")
(test (v*s-v ((interp (lamC (list 'x 'y) (numC 3)) test-env) test-sto))
      (v*s-v (v*s (cloV (list 'x 'y) (numC 3) test-env) empty-store)))
(test (v*s-v ((interp (array-refC (idC 'a) (numC 1)) test-env) test-sto))
      (v*s-v (v*s (numV 110) test-sto)))
(test (v*s-v ((interp (array-refC (idC 'b) (numC 1)) test-env) test-sto))
      (v*s-v (v*s (numV 150) test-sto)))
; (test (v*s-v ((interp (arrayC (list (numC 1) (numC 2) (numC 3))) test-env) test-sto))
;       (v*s-v (v*s (arrayV 3 3) empty-store)))

; (test (v*s-v ((interp (array-refC (idC 'a) (numC 3)) test-env) test-sto))
;       (v*s-v (v*s (numV 12) empty-store)))
; (test )
; (test ((interp (appC (lamC (list 'z 'y) (binopC '+ (idC 'z) (idC 'y)))
;                     (list (binopC '+ (numC 9) (numC 14)) (numC 98))) 
;               empty-env)
;       empty-store)
;       (v*s-v (v*s (numV 121) empty-store)))
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
    [arrayV (loc len) 
      (string-append (string-append "location " (to-string loc))
                     (string-append " length " (to-string len)))]
    [nullV () "null"]))

(test (serialize (numV 4)) "4")
(test (serialize (boolV true)) "true")
(test (serialize (boolV false)) "false")
(test (serialize (cloV (list 'x 'y) (binopC '+ (numC 3) (numC 4)) empty-env)) 
                 "#<procedure>")
(test (serialize (arrayV 5 4))
                 "location 5 length 4")
(test (serialize (nullV)) "null")

; consumes an expression and parses and interprets it
; taken from Assignment 3 by John Clements
(define (top-eval [s : s-expression]) : string
  (serialize (v*s-v ((interp (parse s) empty-env) empty-store))))

; ; taken from Assignment 3 by John Clements
(test (top-eval '{+ 12 4}) "16")
(test (top-eval '{* 12 4}) "48")
(test (top-eval '{- 12 4}) "8")
(test (top-eval '{/ 12 4}) "3")
(test (top-eval `true) "true")
(test (top-eval `false) "false")
; (test (top-eval '{if true 3 4}) "3")
; (test (top-eval '{if true {+ 8 8} {+ 1 1}}) "16")
; (test (top-eval '{{func {z y} {+ z y}} {+ 9 14} 98}) "121")
; (test (top-eval '{with {z = {+ 9 14}}
;                        {y = 98}
;                        {+ z y}})
;       "121")





