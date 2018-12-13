#lang racket/base

(require
  racket/list
  syntax/parse/define
  (for-syntax
   racket/base
   racket/pretty
   (rename-in syntax-generic2 [define-syntax-generic define-syntax-interface] [generics implement])
   syntax/stx
   syntax/id-table
   (rename-in syntax/parse [define/syntax-parse def/stx])))

; Helpers that will eventually be part of the library

(define-simple-macro 
  (define-form (name:id pat ...)
    [(method:id args:id ...)
     body body* ...] ...)
  (define-syntax name
    (implement
     [method (lambda (stx args ...)
               (syntax-parse stx
                 [(name pat ...)
                  body body* ...]))]
     ...)))

(begin-for-syntax
  (define (bind! name binding ctx)
    ; local 3D syntax is fine, right?
    (syntax-local-bind-syntaxes (list name) (and binding #`#,binding) ctx)
    (let ([res (internal-definition-context-introduce ctx name 'add)])
      (record-binding! res)
      res)))

; Actual stuff defining a lambda calculus expander

(begin-for-syntax
  (define-syntax-interface lam-core
    (lambda (stx)
      (raise-syntax-error 'lam "not a lambda calculus core form" stx)))
  (define-syntax-interface lam-var
    (lambda (stx)
      (raise-syntax-error 'lam "not a lambda calculus variable" stx)))

  ; Only need one instance of the RHS, because we're really only using it as a flag...
  (define lam-var-binding
    (implement
     [lam-var (lambda (stx) stx)]))

  ; Jobs of the core dispatch loop:
  ;  * Translate the minimal concrete syntax of references and applications to abstract syntax
  ;  * Dispatch to core forms and transformers.
  (define (expand-lam stx [ctx #f])
    (cond
      [(lam-core? stx)
       (apply-as-transformer lam-core 'expression ctx stx)]
      [else (raise-syntax-error 'lam "not a lambda calculus expression" stx)])))

(define-form (lam-ref x:id)
  [(lam-core)
   (unless (lam-var? #'x)
     (raise-syntax-error 'lam "unbound reference" #'x))
   #`(lam-ref x)])

(define-form (lam-λ (x:id) e)
  [(lam-core)
   (define ctx (syntax-local-make-definition-context))
   (def/stx x^ (bind! #'x lam-var-binding ctx))
   (def/stx e^ (expand-lam #'e ctx))
   #`(lam-λ (x^) e^)])

(define-form (lam-app e1 e2)
  [(lam-core)
   (def/stx e1^ (expand-lam #'e1))
   (def/stx e2^ (expand-lam #'e2))
   #`(lam-app e1^ e2^)])
  
(define-syntax (lam stx)
  (syntax-parse stx
    [(_ e)
     (def/stx e^ (expand-lam #'e))
     #`(quote e^)]))

(lam (lam-λ (x) (lam-ref x)))
