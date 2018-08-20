#lang racket/base

(require

  json
  racket/list
  racket/system
  
  
  (for-syntax
   racket/base
   racket/pretty
   syntax-generic2
   syntax/stx
   syntax/id-table
   (rename-in syntax/parse [define/syntax-parse def/stx])
   ))


(define-syntax-rule 
  (define-syntax/generics (name pat ...)
    [(method args ...)
     body body* ...] ...)
  (define-syntax name
    (generics
     [method (lambda (stx args ...)
               (syntax-parse stx
                 [(name pat ...)
                  body body* ...]))]
     ...)))

(begin-for-syntax
  (define ((expand-to-error message) stx . rest)
    (raise-syntax-error #f message stx))
  
  (define-syntax-generic js-core-expression
    (expand-to-error "not a js core expression"))
  (define-syntax-generic js-core-statement-pass1
    (expand-to-error "not a js core statement"))
  (define-syntax-generic js-core-statement-pass2
    (expand-to-error "not a js core statement"))
  (define-syntax-generic js-variable
    (expand-to-error "not a js variable"))
  (define-syntax-generic js-transformer
    (expand-to-error "not a js form"))

  (define-syntax-generic extract-js-expression
    (lambda (stx idmap)
      (syntax-parse stx
        [x:id (extract-id #'x idmap)]
        [n:number
         (hasheq
          'type "Literal"
          'value (syntax->datum #'n))]
        [_
         (raise-syntax-error 'extract-js "form does not support compilation to JS" stx)])))

  (define-syntax-generic extract-js-statement
    (lambda (stx idmap)
      (let ([res (extract-js-expression stx idmap)])
        (hasheq
         'type "ExpressionStatement"
         'expression res))))

  (define js-var
    (generics
     [js-variable (lambda (stx) stx)]))
  
  (define (js-expand-expression stx ctx)
    (syntax-parse stx
      [_ #:when (js-transformer? stx)
         (js-expand-expression (apply-as-transformer js-transformer 'expression ctx stx) ctx)]
      [_ #:when (js-core-expression? stx)
         (apply-as-transformer js-core-expression 'expression ctx stx)]
      [_ #:when (js-core-statement-pass1? stx)
         (raise-syntax-error #f "js statement not valid in js expression position" stx)]
      [x:id #:when (js-variable? stx)
            stx]
      [n:number stx]
      [(e ...)
       (with-syntax ([app (datum->syntax stx '#%js-app)])
         (js-expand-expression #'(app e ...) ctx))]
      [else
       (raise-syntax-error #f "not a js expression" stx)]))

  ; local-expand with 'expression ensures use-site scopes added to this point aren't deleted
  ;  upon syntax-local-identifier-as-binder within. Might be a problem here... local-apply-transformer
  ;  supports the right thing, but apply-as-transformer doesn't.
  (define (js-expand-statement-pass1 stx ctx)
    (syntax-parse stx
      [_ #:when (js-transformer? stx)
         (js-expand-statement-pass1 (apply-as-transformer js-transformer (list ctx) ctx stx) ctx)]
      [_ #:when (js-core-statement-pass1? stx)
         (apply-as-transformer js-core-statement-pass1 (list ctx) ctx stx ctx)]
      ; Assume it's an expression; we'll expand those in pass 2.
      [_ stx]))

  (define (js-expand-statement-pass2 stx ctx)
    (syntax-parse stx
      [_ #:when (js-core-statement-pass2? stx)
         (apply-as-transformer js-core-statement-pass2 (list ctx) ctx stx)]
      [_ (js-expand-expression stx ctx)]))

  (define (expand-block body ctx)
    (define body^
      (for/list ([b (syntax->list ((make-syntax-introducer #f) body))])
        (js-expand-statement-pass1 b ctx)))
    (for/list ([b body^])
      (js-expand-statement-pass2 b ctx)))

  (struct idmap (table [ctr #:mutable]))
  (define (make-idmap)
    (idmap (make-free-id-table) 0))
  
  (define (extract-id id map)
    (define name
      (let ([v (free-id-table-ref! (idmap-table map) id (lambda () #f))])
        (or v
            (let ([v (string-append (symbol->string (syntax->datum id))
                                    (number->string (idmap-ctr map)))])
              (free-id-table-set! (idmap-table map) id v)
              (set-idmap-ctr! map (+ (idmap-ctr map) 1))
              v))))
    (hasheq 'type "Identifier" 'name name))

  (define (extract-block body idmap)
    (hasheq
     'type "BlockStatement"
     'body (stx-map (λ (b) (extract-js-statement b idmap))
                    body)))
  )


(define (runjs estree)
  (define f (fifth (process*/ports
                    (current-output-port)
                    (open-input-string (jsexpr->string estree))
                    (current-error-port)
                    "/usr/local/bin/node"
                    "runjs.js")))
  (f 'wait)
  (void))

(define-syntax js
  (syntax-parser
    [(_ arg)
     (def/stx expanded-js (extract-js-expression (js-expand-expression #'arg #f) (make-idmap)))
     #'(begin
         (define wrapped (hash 'type "ExpressionStatement" 'expression 'expanded-js))
         ;(pretty-display wrapped)
         (runjs wrapped))]))

(define-syntax/generics (#%js-app e e* ...)
  [(js-core-expression)
   (def/stx (e^ e*^ ...)
     (stx-map (lambda (stx) (js-expand-expression stx #f)) #'(e e* ...)))
   #'(#%js-app e^ e*^ ...)]
  [(extract-js-expression idmap)
   (hasheq
    'type "CallExpression"
    'callee (extract-js-expression #'e idmap)
    'arguments (stx-map (λ (e) (extract-js-expression e idmap)) #'(e* ...)))])

(define-syntax/generics (function (x ...) body ...)
  [(js-core-expression)
   (define ctx (syntax-local-make-definition-context))
   (for ([x (syntax->list #'(x ...))])
     (syntax-local-bind-syntaxes (list x) #`#,js-var ctx))
   (def/stx (x^ ...) (internal-definition-context-introduce ctx #'(x ...)))
   (def/stx (body^ ...)
     (expand-block #'(body ...) ctx))   
   #'(function (x^ ...) body^ ...)]
  [(extract-js-expression idmap)
   (hasheq
    'type "FunctionExpression"
    'params (stx-map (λ (x) (extract-id x idmap)) #'(x ...))
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (let x e)
  [(js-core-statement-pass1 ctx)
   (def/stx x^ (internal-definition-context-introduce ctx (syntax-local-identifier-as-binding #'x)))
   (syntax-local-bind-syntaxes (list #'x^) #`#,js-var ctx)
   #'(let x^ e)]
  [(js-core-statement-pass2)
   (def/stx e^ (js-expand-expression #'e #f))
   #'(let x e^)]
  [(extract-js-statement idmap)
   (hasheq
    'type "VariableDeclaration"
    'kind "let"
    'declarations
    (list (hasheq
           'type "VariableDeclarator"
           'id (extract-id #'x idmap)
           'init (extract-js-expression #'e idmap))))])

(define-syntax/generics (let-syntax m e)
  [(js-core-statement-pass1 ctx)
   (def/stx m^ (internal-definition-context-introduce ctx (syntax-local-identifier-as-binding #'m)))
   (syntax-local-bind-syntaxes (list #'m^) #'(generics
                                              [js-transformer e]) ctx)
   #'5])
   
(define-syntax/generics (return e)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (def/stx e^ (js-expand-expression #'e #f))
   #'(return e^)]
  [(extract-js-statement idmap)
   (hasheq
    'type "ReturnStatement"
    'argument (extract-js-expression #'e idmap))])

(define-syntax/generics (set! var:id e)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   #:fail-unless (js-variable? #'var) (format "expected variable")
   (def/stx e^ (js-expand-expression #'e #f))
   #'(set! var e^)]
  [(extract-js-expression idmap)
   (hasheq
    'type "AssignmentExpression"
    'operator "="
    'left (extract-id #'var idmap)
    'right (extract-js-expression #'e idmap))])

(define-syntax/generics (while condition body ...)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (define ctx (syntax-local-make-definition-context))
   (def/stx condition^ (js-expand-expression #'condition #f))
   (def/stx (body^ ...) (expand-block #'(body ...) ctx))
   #'(while condition^ body^ ...)]
  [(extract-js-statement idmap)
   (hasheq
    'type "WhileStatement"
    'test (extract-js-expression #'condition idmap)
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (if c (b1 ...) (b2 ...))
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (def/stx c^ (js-expand-expression #'c #f))
   (def/stx (b1^ ...) (expand-block #'(b1 ...) (syntax-local-make-definition-context)))
   (def/stx (b2^ ...) (expand-block #'(b2 ...) (syntax-local-make-definition-context)))
   #'(if c^ (b1^ ...) (b2^ ...))]
  [(extract-js-statement idmap)
   (hasheq
    'type "IfStatement"
    'test (extract-js-expression #'c idmap)
    'consequent (extract-block #'(b1 ...) idmap)
    'alternate (extract-block #'(b2 ...) idmap))])

(define-syntax/generics (? c e1 e2)
  [(js-core-expression)
   (def/stx c^ (js-expand-expression #'c #f))
   (def/stx e1^ (js-expand-expression #'e1 #f))
   (def/stx e2^ (js-expand-expression #'e2 #f))
   #'(? c^ e1^ e2^)]
  [(extract-js-expression idmap)
   (hasheq
    'type "ConditionalExpression"
    'test (extract-js-expression #'c idmap)
    'consequent (extract-js-expression #'e1 idmap)
    'alternate (extract-js-expression #'e2 idmap))])


(define-syntax-rule
  (binop op)
  (define-syntax/generics (op e1 e2)
    [(js-core-expression)
     #`(op #,(js-expand-expression #'e1 #f) #,(js-expand-expression #'e2 #f))]
    [(extract-js-expression idmap)
     (hasheq
      'type "BinaryExpression"
      'operator (symbol->string (syntax->datum #'op))
      'left (extract-js-expression #'e1 idmap)
      'right (extract-js-expression #'e2 idmap))]))

(binop +)
(binop *)
(binop -)
(binop /)
(binop <)
(binop <=)
(binop >)
(binop >=)
(binop ==)

; Finally, some macros!
(define-syntax cond
  (generics
   [js-transformer
    (syntax-parser
      #:literals (else)
      [(cond [else e])
       #'e]
      [(cond [c e] clause ...)
       #'(? c e (cond clause ...))])]))

(define-syntax inc!
  (generics
   [js-transformer
    (syntax-parser
      [(_ v)
       #'(set! v (+ 1 v))])]))

(define-syntax defn
  (generics
   [js-transformer
    (syntax-parser
      [(_ (name args ...) body ...)
       #'(let name (function (args ...) body ...))])]))



(module+ test
  (js ((function ()
                 (let factorial (function (n)
                                          (if (<= n 1)
                                              ((return 1))
                                              ((return (* n (factorial (- n 1))))))))
                 (return (factorial 5)))))
  
  (js ((function ()
                 (defn (factorial n)
                   (return (? (<= n 1) 1 (* n (factorial (- n 1))))))
                 (return (factorial 5)))))
  

  (js ((function ()
                 (let factorial (function (n)
                                          (let i 1)
                                          (let res 1)
                                          (while (<= i n)
                                                 (set! res (* res i))
                                                 (inc! i))
                                          (return res)))
                 (return (factorial 5)))))

  (js ((function ()
                 (let fib (function (n)
                                    (return
                                     (cond
                                       [(== n 1) 1]
                                       [(== n 2) 1]
                                       [else (+ (fib (- n 1)) (fib (- n 2)))]))))
                 (return (fib 6)))))
  
  (js ((function ()
                 (let x 5)
                 (let-syntax m (lambda (stx)
                                 (syntax-parse stx
                                   [(_ arg)
                                    #'((function (arg) (return x)) 6)])))
                 (return (m x)))))
  
  )
