#lang plai-typed

(require (typed-in racket
                   [number->string : (number -> string)]))
(require plai-typed/s-exp-match)

(print-only-errors #t)