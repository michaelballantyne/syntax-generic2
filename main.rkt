#lang racket/base

(require
  syntax/apply-transformer
  racket/syntax
  syntax/parse
  (for-syntax
   racket/base
   syntax/parse
   racket/syntax
   syntax/transformer)
  (for-template racket/base))

(provide
 qstx/rc
 
 with-disappeared-uses-and-bindings
 record-disappeared-bindings
 
 unbound
 racket-variable

 scope?
 make-expression-scope
 make-definition-scope
 defctx->scope
 scope-bind!
 scope-lookup
 
 apply-as-transformer
 
 define-syntax-generic
 generics
 (for-syntax syntax-generic-info-prop)

 generics/parse
 )

(define-syntax (qstx/rc stx)
  (syntax-case stx ()
    [(_ template)
     #`(datum->syntax (quote-syntax #,stx)
                      (syntax-e (quasisyntax template))
                      this-syntax this-syntax)]))

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

; Higher-level APIs for scope and binding. Not sure where these should
; live, ultimately.

(struct scope [defctx introducers definition-scope?])

(define (make-expression-scope [parent #f])
  (make-scope 'make-expression-scope #f parent))
(define (make-definition-scope [parent #f])
  (make-scope 'make-definition-scope #t parent))

(define (make-scope fn-name definition-scope? parent)
  (unless (or (eq? #f parent) (scope? parent))
    (raise-argument-error
     fn-name
     "(or/c scope? #f)"
     parent))
  (scope (if parent
             (scope-defctx parent)
             (syntax-local-make-definition-context))
         (cons (make-syntax-introducer #t)
               (if parent
                   (scope-introducers parent)
                   '()))
         definition-scope?))

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
  (unless (scope? sc)
    (raise-argument-error
     'scope-bind!
     "scope?"
     sc))
  (unless (identifier? id)
    (raise-argument-error
     'scope-bind!
     "identifier?"
     id))
  
  (define id-in-sc (syntax-local-identifier-as-binding (in-scope sc id)))
  
  (syntax-local-bind-syntaxes
   (list id-in-sc)
   (cond
     [(syntax? rhs) rhs]
     [(eq? racket-variable rhs) #f]
     [else (datum->syntax (quote-syntax here) (list 'quote rhs))])
   (scope-defctx sc))
  
  (record-disappeared-bindings id-in-sc)
  
  id-in-sc)

(define (defctx->scope defctx definition-scope?)
  (unless (internal-definition-context? defctx)
    (raise-argument-error
     'defctx->scope
     "internal-definition-context?"
     defctx))
  (unless (boolean? definition-scope?)
    (raise-argument-error
     'defctx->scope
     "boolean?"
     definition-scope?))
  (scope defctx '() definition-scope?))

; Apply as transformer. Perhaps should eventually be added to
; syntax/apply-transformer?

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

(define (apply-as-transformer f sc . args)
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
     (if sc
         (if (scope-definition-scope? sc)
             (list (scope-defctx sc))
             'expression)
         (syntax-local-context))
     (if sc (list (scope-defctx sc)) '())))
  
  (apply values (map unwrap (syntax->list res))))

; Syntax generics. eventually syntax/generic?

(begin-for-syntax
  (struct syntax-generic-info [prop func]
    #:property prop:procedure
    (lambda (s stx)
      ((set!-transformer-procedure
        (make-variable-like-transformer (syntax-generic-info-func s))) stx))))

(define (dispatch-on-head stx)
  (syntax-case stx ()
    [v (identifier? #'v) #'v]
    [(v . rest) (identifier? #'v) #'v]
    [_ #f]))

(define (make-generic gen-name pred-name dispatch-on fallback-proc)
  (define-values (prop prop-pred prop-ref) (make-struct-type-property gen-name))

  (define (get-procedure stx-arg sc)
    (define head (dispatch-on stx-arg))
    (and head
         (let ([v (scope-lookup sc head)])
           (and (prop-pred v)
                ((prop-ref v) v)))))

  ; Doesn't take a scope, because we assume this is used with apply-as-transformer.
  ; TODO: bake in apply-as-transformer?
  (define (dispatch stx-arg . args)
    (unless (syntax? stx-arg)
      (raise-argument-error
       gen-name
       "syntax?"
       stx-arg))
    (apply (or (get-procedure stx-arg #f) fallback-proc)
           stx-arg args))

  (define (predicate stx-arg [sc #f]) ; sc for access to bindings in a local context
    (unless (syntax? stx-arg)
      (raise-argument-error
       pred-name
       "syntax?"
       stx-arg))
    (unless (or (eq? sc #f) (scope? sc))
      (raise-argument-error
       pred-name
       "(or/c scope? #f)"
       sc))
    (if (get-procedure stx-arg sc) #t #f))

  (values prop dispatch predicate))

(define ((expand-to-error name) stx . rest)
  (raise-syntax-error #f (format "not a ~a" name) stx))

(define-syntax define-syntax-generic
  (syntax-parser
    [(_ gen-name:id
        (~optional fallback-proc:expr
                   #:defaults ([fallback-proc #'(expand-to-error 'gen-name)]))
        (~optional (~seq #:dispatch-on dispatch-on-e:expr)
                   #:defaults ([dispatch-on-e #'dispatch-on-head])))
     (with-syntax ([gen-name? (format-id #'gen-name "~a?" #'gen-name)])
       #'(begin
           (define-values (prop func gen-name?)
             (make-generic 'gen-name 'gen-name? dispatch-on-e fallback-proc))
           (define-syntax gen-name (syntax-generic-info (quote-syntax prop) (quote-syntax func)))))]))

(define (not-an-expression stx)
  (raise-syntax-error #f "not an expression" stx))

(define (make-generics-impl props)
  (let-values ([(s-decl s s? get-s set-s)
                (make-struct-type 'anonymous #f 0 0 #f props)])
    (s)))

(define-syntax generics
  (syntax-parser
    [(_ (~alt (~optional [(~literal expand) expander]
                         #:defaults ([expander #'not-an-expression]))
              [gen:id func:expr]
              (~seq #:property prop:expr prop-val:expr)) ...)
     (define (get-prop gen-id)
       (define (error)
         (raise-syntax-error
          #f
          "expected reference to syntax generic"
          this-syntax
          gen-id))
       (let ([v (syntax-local-value gen-id error)])
         (or (and (syntax-generic-info? v) (syntax-generic-info-prop v))
             (error))))
     (with-syntax ([(gen-prop ...) (map get-prop (syntax->list #'(gen ...)))])
       ; Use this instead of the struct macro for faster expansion.
       #'(make-generics-impl (list (cons prop:procedure (lambda (s stx) (expander stx)))
                                   (cons gen-prop (lambda (st) func)) ...
                                   (cons prop prop-val) ...)))]))

(define-syntax generics/parse
  (syntax-parser
    [(_ (name:id pat ...)
        [(method:id args:id ...)
         body body* ...] ...)
     ; This trick with the syntax class means that all the pattern
     ; bindings get their hygiene from `name`, rather than their
     ; original syntax.
     #:with empty (datum->syntax #'name '||)
     #'(let ()
         (define-syntax-class cls
           (pattern (name pat ...)))
         (generics
          [method (lambda (stx args ...)
                    (syntax-parse stx
                      [(~var empty cls)
                       body body* ...]))]
          ...))]))