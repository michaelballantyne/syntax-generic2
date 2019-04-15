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

 
 bind!
 make-def-ctx
 make-scope
 scope?
 scope-introducer
 add-scope
 add-scopes
 unbound
 lookup
 
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


; Light wrappers around the scope and definition context APIs for convenience
; and automatic disappeared tracking. It would be really nice to make something
; like these part of the standard library...

(struct scope [introducer])

(define (make-scope) (scope (make-syntax-introducer #t)))

(define (add-scope stx sc)
  (unless (syntax? stx)
    (raise-argument-error
     'add-scope
     "syntax?"
     stx))
  (unless (scope? sc)
    (raise-argument-error
     'add-scope
     "scope?"
     sc))
  ((scope-introducer sc) stx 'add))

(define (add-scopes stx scs)
  (unless (syntax? stx)
    (raise-argument-error
     'add-scopes
     "syntax?"
     stx))
  (unless (and (list? scs) (andmap scope? scs))
    (raise-argument-error
     'add-scopes
     "(listof scope?)"
     scs))
  
  (for/fold ([stx stx])
            ([sc scs])
    ((scope-introducer sc) stx 'add)))


(define (make-def-ctx) (syntax-local-make-definition-context))

(define (add-ctx-scope ctx stx)
  (if ctx
      (internal-definition-context-introduce ctx stx 'add)
      stx))

(define (bind! ctx id rhs)
  (unless (internal-definition-context? ctx)
    (raise-argument-error
     'bind!
     "internal-definition-context?"
     ctx))
  (unless (identifier? id)
    (raise-argument-error
     'bind!
     "identifier?"
     id))
  (unless (or (not rhs) (syntax? rhs))
    (raise-argument-error
     'bind!
     "(or/c #f syntax?)"
     rhs))
  
  (syntax-local-bind-syntaxes (list id) rhs ctx)
  (define id-in-sc (add-ctx-scope ctx (syntax-local-identifier-as-binding id)))
  (record-disappeared-bindings id-in-sc)
  id-in-sc)

; used only for eq? equality.
(define unbound
  (let ()
    (struct unbound [])
    (unbound)))

(define (lookup ctx id)
  (unless (or (not ctx) (internal-definition-context? ctx))
    (raise-argument-error
     'lookup
     "(or/c #f internal-definition-context?)"
     ctx))
  (unless (identifier? id)
    (raise-argument-error
     'lookup
     "identifier?"
     id))
  
  (define id-in-sc (add-ctx-scope ctx id))
  (define result
    (syntax-local-value
     id-in-sc
     (lambda () unbound)
     ctx))

  (unless (eq? result unbound)
    (record-disappeared-uses id-in-sc))
  
  result)

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

(define (apply-as-transformer f ctx-type ctx . args)
  (unless (procedure? f)
    (raise-argument-error
     'apply-as-transformer
     "procedure?"
     f))
  #;(unless (or (eq? #f sc) (scope? sc))
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
     (datum->syntax #f (map wrap args))
     ctx-type
     (cond
       [(internal-definition-context? ctx) (list ctx)]
       [(list? ctx) ctx]
       [(not ctx) '()]
       [else (raise-argument-error
              'apply-as-transformer
              "(or/c internal-definition-context? (listof internal-definition-context?) #f)"
              ctx)])))
  
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
         (let ([v (lookup sc head)])
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
    (unless (or (eq? sc #f) (internal-definition-context? sc))
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
        (~optional (~seq #:dispatch-on dispatch-on-e:expr)
                   #:defaults ([dispatch-on-e #'dispatch-on-head])))
     (with-syntax ([gen-name? (format-id #'gen-name "~a?" #'gen-name)])
       #'(begin
           (define-values (prop func gen-name?)
             (make-generic 'gen-name 'gen-name? dispatch-on-e
                           (expand-to-error 'gen-name)))
           (define-syntax gen-name
             (syntax-generic-info (quote-syntax prop) (quote-syntax func)))))]))

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
              [gen:id func:expr]) ...)
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
       #'(make-generics-impl
          (list (cons prop:procedure (lambda (s stx) (expander stx)))
                (cons gen-prop (lambda (st) func)) ...)))]))

(define-syntax generics/parse
  (syntax-parser
    [(_ pat
        [(method:id args:id ...)
         body body* ...] ...)
     #'(generics
        [method (lambda (stx args ...)
                  (syntax-parse stx
                    [pat
                     body body* ...]))]
        ...)]))