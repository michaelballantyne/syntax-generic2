#lang racket/base

(require
  syntax/parse/define
  (for-syntax racket/base syntax/parse syntax-generic2))

(provide define-syntax/generics)

(define-simple-macro 
  (define-syntax/generics (name:id pat ...)
    [(method:id args:id ...)
     body body* ...] ...)
  (define-syntax name
    (generics
     [method (lambda (stx args ...)
               (syntax-parse stx
                 [(name pat ...)
                  body body* ...]))]
     ...)))