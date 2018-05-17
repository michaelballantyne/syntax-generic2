#lang racket/base

(require "../main.rkt"
         syntax/macro-testing
         rackunit
         (for-syntax racket/base))

(begin-for-syntax
  (define-syntax-generic foo
    (lambda (stx) 'fallback)))

(define-syntax/generics bar
  (lambda (stx) (raise-syntax-error "bad" stx))
  [foo (lambda (stx) 'bar)])

(check-equal? 'bar (phase1-eval (foo #'(bar)) #:catch? #t))
(check-equal? 'bar (phase1-eval (foo #'(bar other (stuff))) #:catch? #t))
(check-equal? 'bar (phase1-eval (foo #'bar) #:catch? #t))

; Unbound
(check-equal? 'fallback (phase1-eval (foo #'baz) #:catch? #t))
(check-equal? 'fallback (phase1-eval (foo #'(baz)) #:catch? #t))

; Bound, as syntax, but without prop
(check-equal? 'fallback (phase1-eval (foo #'cond) #:catch? #t))

; Arity is not static
(define-syntax/generics extra-arg
  (lambda (stx) (raise-syntax-error "bad" stx))
  [foo (lambda (stx arg2) 'extra-arg)])

(check-equal? 'extra-arg (phase1-eval (foo #'extra-arg 'extra) #:catch? #t))

(check-exn
  exn:fail?
  (lambda ()
    (phase1-eval (foo #'extra-arg) #:catch? #t)))

