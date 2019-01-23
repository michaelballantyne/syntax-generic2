#lang racket/base

(require
  syntax-generic2/define
  (for-syntax
   racket/base
   syntax-generic2
   syntax/parse
   ))

(begin-for-syntax
  (define-syntax-generic infix
    #:dispatch-on (syntax-parser [(e1 op:id e2) #'op]))

  (define (expand stx)
    (syntax-parse stx
      [(e1 op:id e2)
       (apply-as-transformer infix #f stx)]))
  )


(define-syntax lang
  (syntax-parser
    [(_ body)
     (expand #'body)]))


(define-syntax ++
  (generics
   [infix
    (syntax-parser
      [(e1 op:id e2)
       #'(+ e1 e2)])]))


(lang (1 ++ 2))