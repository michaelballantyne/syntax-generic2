#lang racket/base

(require
  syntax/parse/define
  (for-syntax racket/base syntax/parse syntax-generic2))

(provide define-syntax/generics)

(define-simple-macro 
  (define-syntax/generics (name:id pat ...)
    [(method:id args:id ...)
     body body* ...] ...)
  #:with empty (datum->syntax this-syntax '||)
  (begin
    ; Could export this; right now it's lifted out just for expansion performance.
    (begin-for-syntax
      (define-syntax-class cls
        (pattern (name pat ...))))
    (define-syntax name
      (generics
       [method (lambda (stx args ...)
                 (syntax-parse stx
                   [(~var empty cls)
                    body body* ...]))]
       ...))))