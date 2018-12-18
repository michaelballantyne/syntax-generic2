#lang racket/base

(require
  syntax/parse
  syntax/apply-transformer
  racket/syntax
  (for-syntax
   racket/base
   syntax/parse
   syntax/transformer
   racket/syntax)
  (for-template racket/base))

(provide 
 with-disappeared-uses-and-bindings
 record-disappeared-bindings
 
 unbound
 racket-variable

 scope?
 make-scope
 defctx->scope
 scope-bind!
 scope-lookup
 
 apply-as-transformer
 
 define-syntax-generic
 generics
 syntax-generic-prop
 )

; racket/syntax currently has tools for disappeared uses,
; but not disappeared bindings. This is a copy-paste-and-modify job
; that should be integrated into a future release of that collection.
  
(define current-recorded-disappeared-bindings (make-parameter #f))

(define (record-disappeared-bindings ids)
  (cond
    [(identifier? ids) (record-disappeared-bindings (list ids))]
    [(and (list? ids) (andmap identifier? ids))
     (let ([uses (current-recorded-disappeared-bindings)])
       (when uses
         (current-recorded-disappeared-bindings 
          (append
           (if (syntax-transforming?)
               (map syntax-local-introduce ids)
               ids)
           uses))))]
    [else (raise-argument-error 'record-disappeared-bindings
                                "(or/c identifier? (listof identifier?))"
                                ids)]))

(define-syntax-rule (with-disappeared-bindings body-expr ... stx-expr)
  (let-values ([(stx disappeared-bindings)
                (parameterize ((current-recorded-disappeared-bindings null))
                  (let ([result (let () body-expr ... stx-expr)])
                    (values result (current-recorded-disappeared-bindings))))])
    (syntax-property stx
                     'disappeared-binding
                     (append (or (syntax-property stx 'disappeared-binding) null)
                             disappeared-bindings))))

(define-syntax-rule (with-disappeared-uses-and-bindings body-expr ... stx-expr)
  (with-disappeared-uses
      (with-disappeared-bindings
          body-expr ... stx-expr)))

; Higher-level APIs for scope and binding

(struct scope [defctx introducers])

(define (make-scope [parent #f])
  (unless (or (eq? #f parent) (scope? parent))
    (raise-argument-error
     'make-scope
     "(or/c scope? #f)"
     parent))
  (scope (if parent
             (scope-defctx parent)
             (syntax-local-make-definition-context))
         (cons (make-syntax-introducer #t)
               (if parent
                   (scope-introducers parent)
                   '()))))

(define (in-scope sc stx)
  (if sc
      (internal-definition-context-introduce
       (scope-defctx sc)
       (for/fold ([stx stx])
                 ([introducer (scope-introducers sc)])
         (introducer stx 'add))
       'add)
      stx))

(define unbound
  (let ()
    (struct unbound [])
    (unbound)))

(define racket-variable
  (let ()
    (struct racket-variable [])
    (racket-variable)))

; Note / TODO: this will consider both out-of-context references and
; identifiers bound to Racket runtime variables as unbound, just
; like syntax-local-value. To do better requires a new expander API,
; as proposed in https://github.com/racket/racket/pull/2300
; A good implementation of that API would implement racket-variable above.
; TODO: should this use a failure-thunk instead of the unbound value?
(define (scope-lookup sc id)
  (unless (or (eq? #f sc) (scope? sc))
    (raise-argument-error
     'scope-lookup
     "(or/c scope? #f)"
     sc))
  (unless (identifier? id)
    (raise-argument-error
     'scope-lookup
     "identifier?"
     id))
  
  (define id-in-sc (in-scope sc id))
  
  (define result
    (syntax-local-value
     id-in-sc
     (lambda () unbound)
     (and sc (scope-defctx sc))))

  (unless (eq? result unbound)
    (record-disappeared-uses id-in-sc))
  
  result)

(define (scope-bind! sc id rhs)
  (unless (or (eq? #f sc) (scope? sc))
    (raise-argument-error
     'scope-bind!
     "(or/c scope? #f)"
     sc))
  (unless (identifier? id)
    (raise-argument-error
     'scope-bind!
     "identifier?"
     id))
  
  (define id-in-sc (in-scope sc id))
  
  (syntax-local-bind-syntaxes
   (list id-in-sc)
   (cond
     [(syntax? rhs) rhs]
     [(eq? racket-variable rhs) #f]
     [else (datum->syntax (quote-syntax here) (list 'quote rhs))])
   (and sc (scope-defctx sc)))
  
  (record-disappeared-bindings id-in-sc)
  
  id-in-sc)

(define (defctx->scope defctx)
  (unless (internal-definition-context? defctx)
    (raise-argument-error
     'defctx->scope
     "internal-definition-context?"
     defctx))
  (scope defctx '()))

; Apply as transformer

(struct wrapper (contents))

(define (wrap arg)
  (if (syntax? arg)
      arg
      (wrapper arg)))

(define (unwrap arg)
  (if (syntax? arg)
      (let ([e (syntax-e arg)])
        (if (wrapper? e)
            (wrapper-contents e)
            arg))
      arg))

(define (apply-as-transformer f ctx-type sc . args)
  (unless (procedure? f)
    (raise-argument-error
     'apply-as-transformer
     "procedure?"
     f))
  (unless (or (eq? #f sc) (scope? sc))
    (raise-argument-error
     'apply-as-transformer
     "(or/c scope? #f)"
     sc))

  (define (single-argument-transformer stx)
    (call-with-values
     (lambda () (apply f (map unwrap (syntax->list stx))))
     (lambda vs (datum->syntax #f (map wrap vs)))))
  
  (define res
    (local-apply-transformer
     single-argument-transformer
     (in-scope sc (datum->syntax #f (map wrap args)))
     ctx-type
     (if sc (list (scope-defctx sc)) '())))
  
  (apply values (map unwrap (syntax->list res))))

; Syntax generics

(define (get-procedure prop-pred prop-ref stx-arg sc)
  (define head
    (syntax-case stx-arg ()
      [v (identifier? #'v) #'v]
      [(v . rest) (identifier? #'v) #'v]
      [_ #f]))
  (and head
       (let ([v (scope-lookup sc head)])
         (and (prop-pred v)
              ((prop-ref v) v)))))

; The predicate may need an extended local context for syntax-local-value
(define ((make-predicate prop-pred prop-ref) stx-arg [sc #f])
  (if (get-procedure prop-pred prop-ref stx-arg sc) #t #f))

(define ((make-dispatch gen-name prop-pred prop-ref fallback) stx-arg . args)
  (define f
    (or (get-procedure prop-pred prop-ref stx-arg #f)
        fallback))
  (apply f stx-arg args))

(begin-for-syntax
  (struct generic-info (prop func)
    #:property prop:procedure
    (lambda (s stx)
      ((set!-transformer-procedure
        (make-variable-like-transformer (generic-info-func s))) stx))))
  
(define-syntax define-syntax-generic
  (syntax-parser
    [(_ name:id
        fallback-proc:expr)
     (define/syntax-parse gen-pred (format-id #'name "~a?" #'name))
     #'(begin
         (define-values (prop pred ref) (make-struct-type-property 'name))
         (define func (make-dispatch 'name pred ref fallback-proc))
         (define gen-pred (make-predicate pred ref))
         (define-syntax name (generic-info #'prop #'func)))]))

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
       (or (and (generic-info? v) (generic-info-prop v))
           (error)))]))

(define (not-an-expression stx)
  (raise-syntax-error #f "not an expression" stx))

(define-syntax generics
  (syntax-parser
    [(_ (~alt (~optional [(~literal expand) expander] #:defaults ([expander #'not-an-expression]))
              [gen:id func:expr]) ...)
     #'(let ()
         (struct s ()
           #:property prop:procedure (lambda (s stx) (expander stx))
           (~@ #:property (syntax-generic-prop gen) (lambda (st) func)) ...)
         (s))]))



