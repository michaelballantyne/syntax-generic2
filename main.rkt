#lang racket/base

(require (for-syntax racket/base syntax/parse)
         (for-meta 2 racket/base syntax/parse syntax/transformer))

(provide (for-syntax define-syntax-generic
                     syntax-generic-prop)
         define-syntax/generics)

(begin-for-syntax
  (define ((make-dispatch gen-name prop-pred prop-ref fallback) stx-arg . args)
    (define v
      (syntax-parse stx-arg
        [v:id
         #'v]
        [(v:id . rest)
         #'v]
        [_ #f]))
    (define f
      (or (and v
               (let ([v (syntax-local-value v (lambda () #f))])
                 (and (prop-pred v)
                      ((prop-ref v) v))))
          fallback))
    (apply f stx-arg args)))

(begin-for-syntax
  (begin-for-syntax
    (struct generic (prop func)
      #:property prop:procedure
      (lambda (s stx)
        ((set!-transformer-procedure
          (make-variable-like-transformer (generic-func s))) stx))))
  
  (define-syntax define-syntax-generic
    (syntax-parser
      [(_ name:id
          fallback-proc:expr)
       #'(begin
           (define-values (prop pred ref) (make-struct-type-property 'name))
           (define func (make-dispatch 'name pred ref fallback-proc))
           (define-syntax name (generic #'prop #'func)))]))

  (define-syntax syntax-generic-prop
    (syntax-parser
      [(_ gen-name)
       (define (error)
         (raise-syntax-error
          #f
          "expected reference to syntax generic"
          this-syntax))
       (let ([v (syntax-local-value
                 #'gen-name
                 error)])
         (or (and (generic? v) (generic-prop v))
             (error)))])))

(define-syntax define-syntax/generics
  (syntax-parser
    [(_ name:id
        expander:expr
        [gen:id func:expr] ...)
     #'(begin
         (begin-for-syntax
           (struct s ()
             #:property prop:procedure (lambda (s stx) (expander stx))
             (~@ #:property (syntax-generic-prop gen) (lambda (st) func)) ...))
         (define-syntax name (s)))]))
