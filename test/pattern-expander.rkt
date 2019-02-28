#lang racket

(require
  syntax-generic2/define
  (for-syntax
   syntax/parse
   syntax-generic2))

(begin-for-syntax
  (define-syntax-generic core-pattern-expand)
  (define-syntax-generic pattern-macro)

  (define (no-dups! l)
    (when (not (null? l))
      (for ([id2 (cdr l)])
        (displayln 'here)
        (displayln (syntax-debug-info (car l)))
        (displayln (syntax-debug-info id2))
        (when (bound-identifier=? (car l) id2)
          (raise-syntax-error 'expand-pattern "duplicate pattern variables" #f #f (list (car l) id2))))
      (no-dups! (cdr l)))) 
  
  (define (expand-pattern stx)
    (cond
      [(core-pattern-expand? stx)
       (define-values (vars p^) (core-pattern-expand stx))
       (no-dups! vars)
       (values vars p^)]
      [(identifier? stx)
       (with-syntax ([#%pattern-var (datum->syntax stx '#%pattern-var)])
         (expand-pattern #`(#%pattern-var #,stx)))]
      [(pattern-macro? stx)
       (expand-pattern (apply-as-transformer pattern-macro 'expression #f stx))]
      [else (raise-syntax-error 'expand-pattern "bad pattern syntax" stx)])))

(define-syntax/generics (#%pattern-var v:id)
  [(core-pattern-expand)
   (values (list (syntax-local-identifier-as-binding #'v)) this-syntax)])

(define-syntax/generics (quote ())
  [(core-pattern-expand)
   (values (list) this-syntax)])

(define-syntax/generics (cons a d)
  [(core-pattern-expand)
   (define-values (a-vars a^) (expand-pattern #'a))
   (define-values (d-vars d^) (expand-pattern #'d))
   (values (append a-vars d-vars) #`(cons #,a^ #,d^))])

(define-syntax list
  (generics
   [pattern-macro (syntax-parser
                    [(_)
                     #'(quote ())]
                    [(_ a a* ...)
                     #'(cons a (list a* ...))])]))

(begin-for-syntax
  #;(displayln (expand-pattern #'(list (cons a d) b c)))
  (define-values (vars p^) (expand-pattern #'(list (cons a b) b c)))
  (displayln vars)
  (displayln p^))