#lang racket/base

(require
  (for-syntax racket/base syntax/parse syntax-generic2))

(provide define-syntax/generics)

(define-syntax define-syntax/generics
  (syntax-parser
    [(_ (name:id pat ...)
        [(method:id args:id ...)
         body body* ...] ...)
     #'(define-syntax name
         (generics/parse (name pat ...)
           [(method args ...)
            body body* ...]
           ...))]))