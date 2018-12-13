#lang racket/base

(require
  syntax-generic2/define
  (for-syntax
   racket/base
   syntax-generic2
   (rename-in syntax/parse [define/syntax-parse def/stx])))

; A lambda calculus expander

(begin-for-syntax
  (define-syntax-generic lam-core
    (lambda (stx)
      (raise-syntax-error 'lam "not a lambda calculus core form" stx)))
  (define-syntax-generic lam-var
    (lambda (stx)
      (raise-syntax-error 'lam "not a lambda calculus variable" stx)))

  ; Only need one instance of the RHS, because we're really only using it as a flag...
  (define lam-var-binding
    (generics
     [lam-var (lambda (stx) stx)]))

  ; Jobs of the core dispatch loop:
  ;  * Translate the minimal concrete syntax of references and applications to abstract syntax
  ;  * Dispatch to core forms and transformers.
  (define (expand-lam stx [ctx #f])
    (cond
      [(lam-core? stx)
       (apply-as-transformer lam-core 'expression ctx stx)]
      [else (raise-syntax-error 'lam "not a lambda calculus expression" stx)])))

(define-syntax/generics (lam-ref x:id)
  [(lam-core)
   (unless (lam-var? #'x)
     (raise-syntax-error 'lam "unbound reference" #'x))
   (record-use! #'x)
   #`(lam-ref x)])

(define-syntax/generics (lam-λ (x:id) e)
  [(lam-core)
   (define ctx (syntax-local-make-definition-context))
   (define sc (make-syntax-introducer))                 ; TODO: too many steps for a binding!
   (def/stx x^ (bind! (sc #'x) lam-var-binding ctx))
   (def/stx e^ (expand-lam (sc #'e) ctx))
   #`(lam-λ (x^) e^)])

(define-syntax/generics (lam-app e1 e2)
  [(lam-core)
   (def/stx e1^ (expand-lam #'e1))
   (def/stx e2^ (expand-lam #'e2))
   #`(lam-app e1^ e2^)])
  
(define-syntax (lam stx)
  (syntax-parse stx
    [(_ e)
     (capture-disappeared
      (lambda ()
        (def/stx e^ (expand-lam #'e))
        #'(quote e^)))]))

(lam (lam-λ (x) (lam-ref x)))
