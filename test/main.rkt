#lang racket/base

(require
  syntax/macro-testing
  rackunit
  (for-syntax "../main.rkt" racket/base))

(begin-for-syntax
  (define-syntax-generic foo
    (lambda (stx) 'fallback)))

(define-syntax bar
  (generics
   [expand (lambda (stx) (raise-syntax-error "bad" stx))]
   [foo (lambda (stx) 'bar)]))

(check-equal? 'bar (phase1-eval (foo #'(bar)) #:catch? #t))
(check-equal? 'bar (phase1-eval (foo #'(bar other (stuff))) #:catch? #t))
(check-equal? 'bar (phase1-eval (foo #'bar) #:catch? #t))

; Unbound
(check-equal? 'fallback (phase1-eval (foo #'baz) #:catch? #t))
(check-equal? 'fallback (phase1-eval (foo #'(baz)) #:catch? #t))

; Bound, as syntax, but without prop
(check-equal? 'fallback (phase1-eval (foo #'cond) #:catch? #t))

; Arity is not static
(define-syntax extra-arg
  (generics 
   [expand (lambda (stx) (raise-syntax-error "bad" stx))]
   [foo (lambda (stx arg2) 'extra-arg)]))

(check-equal? 'extra-arg (phase1-eval (foo #'extra-arg 'extra) #:catch? #t))

(check-exn
 exn:fail?
 (lambda ()
   (phase1-eval (foo #'extra-arg) #:catch? #t)))

