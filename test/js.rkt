#lang racket/base

(require
  json
  racket/list
  racket/system
  syntax/parse/define
  (for-syntax
   racket/base
   racket/pretty
   syntax-generic2
   syntax/stx
   syntax/id-table
   (rename-in syntax/parse [define/syntax-parse def/stx])))

(define-simple-macro 
  (define-syntax/generics (name:id pat ...)
    [(method:id args:id ...)
     body body* ...] ...)
  (define-syntax name
    (generics
     [method (lambda (stx args ...)
               (syntax-parse stx
                 [(name pat ...)
                  body body* ...]))]
     ...)))

(begin-for-syntax
  ; Not sure if this is a good idea, but I'm hoping it will give me
  ; better error messages without being verbose.
  
  (define-syntax-rule (syntax stx) (syntax/loc this-syntax stx))
  (define-syntax-rule (quasisyntax stx) (quasisyntax/loc this-syntax stx))

  ; Expansion

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

  (define js-var-binding
    (generics
     [js-variable (lambda (stx) stx)]))
  
  (define (bind-var! name ctx)
    (syntax-local-bind-syntaxes (list name) (quote-syntax js-var-binding) ctx)
    (let ([res (syntax-local-identifier-as-binding (internal-definition-context-introduce ctx name 'add))])
      (record-binding! res)
      res))

  (define (js-expand-expression stx ctx)
    (syntax-parse stx
      [_ #:when (js-transformer? stx)
         (js-expand-expression (apply-as-transformer js-transformer 'expression ctx stx) ctx)]
      [_ #:when (js-core-expression? stx)
         (apply-as-transformer js-core-expression 'expression ctx stx)]
      [_ #:when (js-core-statement-pass1? stx)
         (raise-syntax-error #f "js statement not valid in js expression position" stx)]

      ; implicits / interposition points
      [x:id
       #:when (js-variable? stx)
       (with-syntax ([var (datum->syntax stx '#%js-var)])
         (js-expand-expression #'(var x) ctx))]
      [n:number
       (with-syntax ([datum (datum->syntax stx '#%js-datum)])
         (js-expand-expression #'(datum n) ctx))]
      [(e ...)
       (with-syntax ([app (datum->syntax stx '#%js-app)])
         (js-expand-expression #'(app e ...) ctx))]
      
      [else
       (raise-syntax-error #f "not a js expression" stx)]))

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

  ; Compilation to JS
  
  (define-syntax-generic extract-js-expression
    (expand-to-error "form does not support compilation to JS"))
  (define-syntax-generic extract-js-statement
    (lambda (stx idmap)
      (hash
       'type "ExpressionStatement"
       'expression (extract-js-expression stx idmap))))
  
  (struct idmap (table [ctr #:mutable]))
  (define (make-idmap)
    (idmap (make-free-id-table) 0))

  (define (extract-binder id map)
    (when (free-id-table-ref! (idmap-table map) id (lambda () #f))
      (raise-syntax-error #f "duplicate binding occurance" id))
    (define name (string-append (symbol->string (syntax->datum id))
                                (number->string (idmap-ctr map))))
    (free-id-table-set! (idmap-table map) id name)
    (set-idmap-ctr! map (+ (idmap-ctr map) 1))
    (hasheq 'type "Identifier" 'name name))
  
  (define (extract-ref id map)
    (define name (free-id-table-ref! (idmap-table map) id
                                     (lambda () (raise-syntax-error #f "unbound identifier" id))))
    (hasheq 'type "Identifier" 'name name))

  (define (extract-block body idmap)
    (hasheq
     'type "BlockStatement"
     'body (stx-map (λ (b) (extract-js-statement b idmap))
                    body))))

; Core expressions

(define-syntax/generics (#%js-var x:id)
  [(js-core-expression) (record-use! #'x) this-syntax]
  [(extract-js-expression idmap)
   (extract-ref #'x idmap)])

(define-syntax/generics (#%js-datum n:number)
  [(js-core-expression) this-syntax]
  [(extract-js-expression idmap)
   (hasheq
    'type "Literal"
    'value (syntax->datum #'n))])

(define-syntax/generics (#%js-app e e* ...)
  [(js-core-expression)
   #`(#%js-app #,(js-expand-expression #'e #f)
               #,@(stx-map (lambda (stx) (js-expand-expression stx #f)) #'(e* ...)))]
  [(extract-js-expression idmap)
   (hasheq
    'type "CallExpression"
    'callee (extract-js-expression #'e idmap)
    'arguments (stx-map (λ (e) (extract-js-expression e idmap)) #'(e* ...)))])

(define-syntax/generics (? c e1 e2)
  [(js-core-expression)
   #`(? #,(js-expand-expression #'c #f)
        #,(js-expand-expression #'e1 #f)
        #,(js-expand-expression #'e2 #f))]
  [(extract-js-expression idmap)
   (hasheq
    'type "ConditionalExpression"
    'test (extract-js-expression #'c idmap)
    'consequent (extract-js-expression #'e1 idmap)
    'alternate (extract-js-expression #'e2 idmap))])

(define-syntax/generics (function (x:id ...) body ...)
  [(js-core-expression)
   (define ctx (syntax-local-make-definition-context))
   (def/stx (x^ ...)
     (for/list ([x (syntax->list #'(x ...))])
       (bind-var! x ctx)))
   (def/stx (body^ ...)
     (expand-block #'(body ...) ctx))
   #'(function (x^ ...) body^ ...)]
  [(extract-js-expression idmap)
   (hasheq
    'type "FunctionExpression"
    'params (stx-map (λ (x) (extract-binder x idmap)) #'(x ...))
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (set! var:id e)
  [(js-core-expression)
   #:fail-unless (js-variable? #'var) (format "expected variable")
   (record-use! #'var)
   #`(set! var #,(js-expand-expression #'e #f))]
  [(extract-js-expression idmap)
   (hasheq
    'type "AssignmentExpression"
    'operator "="
    'left (extract-ref #'var idmap)
    'right (extract-js-expression #'e idmap))])

(define-syntax-rule
  (binop op)
  (define-syntax/generics (op e1 e2)
    [(js-core-expression)
     #`(op #,(js-expand-expression #'e1 #f)
           #,(js-expand-expression #'e2 #f))]
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

; Core statements

(define-syntax/generics (let x:id e)
  [(js-core-statement-pass1 ctx)   
   #`(let #,(bind-var! #'x ctx) e)]
  [(js-core-statement-pass2)
   #`(let x #,(js-expand-expression #'e #f))]
  [(extract-js-statement idmap)
   (hasheq
    'type "VariableDeclaration"
    'kind "let"
    'declarations
    (list (hasheq
           'type "VariableDeclarator"
           'id (extract-binder #'x idmap)
           'init (extract-js-expression #'e idmap))))])

(define-syntax/generics (let-syntax m:id e)
  [(js-core-statement-pass1 ctx)
   (def/stx m^ (internal-definition-context-introduce ctx (syntax-local-identifier-as-binding #'m) 'add))
   (record-binding! #'m^)
   (syntax-local-bind-syntaxes (list #'m^) #'(generics
                                              [js-transformer e]) ctx)
   #'(let-syntax m^ e)]
  [(js-core-statement-pass2) this-syntax]
  [(extract-js-statement idmap)
   (hasheq 'type "EmptyStatement")])
   
(define-syntax/generics (return e)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   #`(return #,(js-expand-expression #'e #f))]
  [(extract-js-statement idmap)
   (hasheq
    'type "ReturnStatement"
    'argument (extract-js-expression #'e idmap))])

(define-syntax/generics (while condition body ...)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (define ctx (syntax-local-make-definition-context))
   #`(while #,(js-expand-expression #'condition #f)
            #,@(expand-block #'(body ...) ctx))]
  [(extract-js-statement idmap)
   (hasheq
    'type "WhileStatement"
    'test (extract-js-expression #'condition idmap)
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (if c (b1 ...) (b2 ...))
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   #`(if #,(js-expand-expression #'c #f)
         #,(expand-block #'(b1 ...) (syntax-local-make-definition-context))
         #,(expand-block #'(b2 ...) (syntax-local-make-definition-context)))]
  [(extract-js-statement idmap)
   (hasheq
    'type "IfStatement"
    'test (extract-js-expression #'c idmap)
    'consequent (extract-block #'(b1 ...) idmap)
    'alternate (extract-block #'(b2 ...) idmap))])

; Interface with Racket

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
     (capture-disappeared
      (lambda ()
        (def/stx expanded-js (extract-js-expression (js-expand-expression #'arg #f) (make-idmap)))
        #'(begin
            (define wrapped (hash 'type "ExpressionStatement" 'expression 'expanded-js))
            ;(pretty-display wrapped)
            (runjs wrapped))))]))

; Finally, some macros! These ones defined outside the language.

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
      [(_ v:id)
       #'(set! v (+ 1 v))])]))

(define-syntax defn
  (generics
   [js-transformer
    (syntax-parser
      [(_ (name:id args:id ...) body ...)
       #'(let name (function (args ...) body ...))])]))


(module+ test
  (js ((function ()
                 (let factorial (function (n)
                                          5 ; expressions are allowed in statement position
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

  ; A macro defined inside the langauge. Also a use-site binder test.
  (js ((function ()
                 (let x 5)
                 (let-syntax m (lambda (stx)
                                 (syntax-parse stx
                                   [(_ arg)
                                    #'((function (arg) (return x)) 6)])))
                 (return (m x)))))
  
  )