#lang racket/base

(require
  syntax/parse
  syntax/apply-transformer
  (for-syntax
   racket/base
   syntax/parse
   syntax/transformer
   racket/syntax)
  (for-template racket/base))

(provide define-syntax-generic
         syntax-generic-prop
         generics
         apply-as-transformer

         record-use!
         record-binding!
         capture-disappeared)

; Tools for recording disappeared uses and bindings
  
(define disappeared-uses (make-parameter #f))
(define disappeared-bindings (make-parameter #f))

(define (record-name! stx b)
  (set-box! b (cons (syntax-property
                     (syntax-local-introduce stx)
                     'original-for-check-syntax #t)
                    (unbox b))))
  
(define (record-use! name)
  (record-name! name (disappeared-uses)))

(define (record-binding! stx)
  (record-name! stx (disappeared-bindings)))

(define (capture-disappeared thunk)
  (parameterize ([disappeared-uses (box null)] [disappeared-bindings (box null)])
    (let ([stx (thunk)])
      (syntax-property
       (syntax-property
        stx
        'disappeared-use (unbox (disappeared-uses)))
       'disappeared-binding (unbox (disappeared-bindings))))))

; Syntax generics

(define (get-procedure prop-pred prop-ref stx-arg)
  (define head
    (syntax-parse stx-arg
      [v:id
       #'v]
      [(v:id . rest)
       #'v]
      [_ #f]))
  (and head
       (let ([v (syntax-local-value head (lambda () #f))])
         (when v (record-use! head))
         (and (prop-pred v)
              ((prop-ref v) v)))))

(define ((make-predicate prop-pred prop-ref) stx-arg)
  (if (get-procedure prop-pred prop-ref stx-arg) #t #f))

(define ((make-dispatch gen-name prop-pred prop-ref fallback) stx-arg . args)
  (define f
    (or (get-procedure prop-pred prop-ref stx-arg)
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

; Apply as transformer

(struct wrapper (contents))
(define (wrap arg)
  (if (syntax? arg)
      arg
      (wrapper arg)))

(define (unwrap arg)
  (if (and (syntax? arg) (wrapper? (syntax-e arg)))
      (wrapper-contents (syntax-e arg))
      arg))

(define (apply-as-transformer f ctx-type ctx . args)
  (define (g stx)
    #`#,(call-with-values (lambda () (apply f (map unwrap (syntax->list stx))))
                          list))
  (define res (local-apply-transformer
               g (datum->syntax #f (map wrap args))
               ctx-type (if ctx (list ctx) '())))
  (apply values (syntax->list res)))


