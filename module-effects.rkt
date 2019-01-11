#lang racket/base

(provide #%top-interaction #%datum #%app (rename-out [test-module-begin #%module-begin]))

(require (for-syntax racket/base racket/syntax racket/control racket/match))

(define-syntax (magic-module-begin stx)
  (syntax-case stx ()
    [(_ f-stx body)
     (let ()
       (define f (syntax-local-eval #'f-stx))
       (define body^ (syntax-local-introduce #'body))
       (define thunk (lambda () (f body^) #'(void)))
       #`(#%module-begin
          (magic-module-begin-trampoline #,thunk)))]))

(begin-for-syntax
  (define macro-effect-tag (make-continuation-prompt-tag))
  (struct eff-define-value [lhs rhs])

  (define (bind-value! lhs rhs)
    ; No syntax-local-introduce, because we're working in positive space in the module-begin macro...
    ; but working in positive space means that we don't get hygiene properly. We could create our own
    ; macro introduction scope and work in negative space with regard to it, but I don't think that
    ; would account for needed use-site scopes. I guess we don't need use-site scopes for a module
    ; begin, though. So the only real problem is that a user calling syntax-local-introduce would get
    ; odd behavior.

    ; Wait... maybe we get hygiene okay, because the names we introduce are already different enough.
    ; They can't come from the module we did a module-begin macro for, right? So the hack gets us
    ; pretty close. I could definitely implement a real langauge this way.
    (call/cc
     (lambda (k)
       (abort/cc macro-effect-tag (eff-define-value lhs rhs) k))
     macro-effect-tag)))

(define-syntax (magic-module-begin-trampoline stx)
  (syntax-case stx ()
    [(_ f)
     (let ()
       (define thunk (syntax->datum #'f))

       (define (handler eff k)
         (match eff
           [(eff-define-value lhs rhs)
            #`(begin
                (define #,(syntax-local-introduce lhs) #,rhs)
                (define x 5)
                (magic-module-begin-trampoline #,k))]))
     
       (call-with-continuation-prompt
        thunk
        macro-effect-tag
        handler))]))

(define-for-syntax (testf stx)
  (syntax-case stx ()
    [([lhs rhs] ...)
     (for ([l (syntax->list #'(lhs ...))]
           [r (syntax->list #'(rhs ...))])
       (bind-value! l r))]))

(define-syntax (test-module-begin stx)
  (syntax-case stx ()
    [(_ body)
     #'(magic-module-begin testf body)]))