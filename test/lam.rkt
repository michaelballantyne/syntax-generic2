#lang racket/base

(require
  syntax-generic2/define
  (for-syntax
   racket/base
   syntax-generic2
   syntax/parse
   (only-in syntax/parse [define/syntax-parse def/stx])))

; A lambda calculus expander

(begin-for-syntax
  (define-syntax-generic lam-core)
  (define-syntax-generic lam-var)
  (define lam-var-binding (generics [lam-var (lambda (stx) stx)]))
  (define (expand-lam stx [ctx #f])
    (cond [(lam-core? stx) (apply-as-transformer lam-core 'expression ctx stx)]
          [else (raise-syntax-error 'lam "not a lambda calculus expression" stx)])))
(define-syntax/generics (lam-ref x:id)
  [(lam-core)
   (unless (lam-var? #'x) (raise-syntax-error 'lam "unbound reference" #'x))
   (qstx/rc (lam-ref x))])
(define-syntax/generics (lam-λ (x:id) e)
  [(lam-core)
   (define ctx (make-def-ctx))
   (define sc (make-scope))
   (def/stx x^ (bind! ctx (add-scope #'x sc) #'lam-var-binding))
   (def/stx e^ (expand-lam (add-scope #'e sc) ctx))
   (qstx/rc (lam-λ (x^) e^))])
(define-syntax/generics (lam-app e1 e2)
  [(lam-core)
   (def/stx e1^ (expand-lam #'e1)) (def/stx e2^ (expand-lam #'e2))
   (qstx/rc (lam-app e1^ e2^))])

(define-syntax (lam stx)
  (syntax-parse stx
    [(_ e)
     (with-disappeared-uses-and-bindings
       (def/stx e^ (expand-lam #'e))
       (qstx/rc (quote e^)))]))

(lam (lam-λ (x) (lam-ref x)))
