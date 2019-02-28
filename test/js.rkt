#lang racket/base

(require
  json
  racket/list
  racket/system
  syntax-generic2/define
  (for-syntax
   racket/base
   syntax-generic2
   syntax/stx
   syntax/id-table
   (rename-in syntax/parse [define/syntax-parse def/stx])))

(begin-for-syntax
  ; Expansion
  
  (define-syntax-generic js-core-expression)
  (define-syntax-generic js-core-statement-pass1)
  (define-syntax-generic js-core-statement-pass2)
  (define-syntax-generic js-variable)
  (define-syntax-generic js-transformer)

  (define the-js-var-binding
    (generics
     [js-variable (lambda (stx) stx)]))
  
  (define (bind-var! ctx name)
    (bind! ctx name #'the-js-var-binding))

  (define (js-expand-expression stx ctx)
    (syntax-parse stx
      [_ #:when (js-transformer? stx ctx)
         (js-expand-expression (apply-as-transformer js-transformer 'expression ctx stx) ctx)]
      [_ #:when (js-core-expression? stx ctx)
         (apply-as-transformer js-core-expression 'expression ctx stx)]
      [_ #:when (js-core-statement-pass1? stx ctx)
         (raise-syntax-error #f "js statement not valid in js expression position" stx)]

      ; implicits / interposition points
      [x:id
       #:when (js-variable? stx ctx)
       (with-syntax ([var (datum->syntax stx '#%js-var)])
         (js-expand-expression (qstx/rc (var x)) ctx))]
      [n:number
       (with-syntax ([datum (datum->syntax stx '#%js-datum)])
         (js-expand-expression (qstx/rc (datum n)) ctx))]
      [(e ...)
       (with-syntax ([app (datum->syntax stx '#%js-app)])
         (js-expand-expression (qstx/rc (app e ...)) ctx))]
      
      [else
       (raise-syntax-error #f "not a js expression" stx)]))

  (define (js-expand-statement-pass1 stx ctx)    
    (syntax-parse stx
      [_ #:when (js-transformer? stx ctx)
         (js-expand-statement-pass1 (apply-as-transformer js-transformer (list ctx) ctx stx) ctx)]
      [_ #:when (js-core-statement-pass1? stx)
         (apply-as-transformer js-core-statement-pass1 (list ctx) ctx stx ctx)]
      ; Assume it's an expression; we'll expand those in pass 2.
      [_ stx]))

  (define (js-expand-statement-pass2 stx ctx)
    (syntax-parse stx
      [_ #:when (js-core-statement-pass2? stx ctx)
         (apply-as-transformer js-core-statement-pass2 (list ctx) ctx stx)]
      [_ (js-expand-expression stx ctx)]))

  (define (expand-block body ctx)
    (define sc (make-scope))
    (define body^
      (for/list ([b (syntax->list body)])
        (js-expand-statement-pass1 (add-scope b sc) ctx)))
    (for/list ([b body^])
      (js-expand-statement-pass2 b ctx)))

  ; Compilation to JS
  
  (define-syntax-generic extract-js-expression)
  (define-syntax-generic extract-js-statement
    (lambda (stx idmap)
      ; If it didn't match as a statement, it should be an expression
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
  [(js-core-expression)
   (when (not (js-variable? #'x))
     (raise-syntax-error #f "unbound identifier" #'x))
   this-syntax]
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
   (qstx/rc (#%js-app #,(js-expand-expression #'e #f)
                      #,@(stx-map (lambda (stx) (js-expand-expression stx #f))
                                  #'(e* ...))))]
  [(extract-js-expression idmap)
   (hasheq
    'type "CallExpression"
    'callee (extract-js-expression #'e idmap)
    'arguments (stx-map (λ (e) (extract-js-expression e idmap)) #'(e* ...)))])

(define-syntax/generics (? c e1 e2)
  [(js-core-expression)
   (qstx/rc (? #,(js-expand-expression #'c #f)
               #,(js-expand-expression #'e1 #f)
               #,(js-expand-expression #'e2 #f)))]
  [(extract-js-expression idmap)
   (hasheq
    'type "ConditionalExpression"
    'test (extract-js-expression #'c idmap)
    'consequent (extract-js-expression #'e1 idmap)
    'alternate (extract-js-expression #'e2 idmap))])

(define-syntax/generics (function (x:id ...) body ...)
  [(js-core-expression)
   (define ctx (make-def-ctx))
   (define sc (make-scope))
   (def/stx (x^ ...)
     (for/list ([x (syntax->list #'(x ...))])
       (bind-var! ctx (add-scope x sc))))
   (def/stx (body^ ...)
     (expand-block (add-scope #'(body ...) sc) ctx))
   #'(function (x^ ...) body^ ...)]
  [(extract-js-expression idmap)
   (hasheq
    'type "FunctionExpression"
    'params (stx-map (λ (x) (extract-binder x idmap)) #'(x ...))
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (set! var:id e)
  [(js-core-expression)
   #:fail-unless (js-variable? #'var) (format "expected variable")
   (qstx/rc (set! var #,(js-expand-expression #'e #f)))]
  [(extract-js-expression idmap)
   (hasheq
    'type "AssignmentExpression"
    'operator "="
    'left (extract-ref #'var idmap)
    'right (extract-js-expression #'e idmap))])

(begin-for-syntax
  (define binop
    (generics
     [js-core-expression
      (syntax-parser
        [(op e1 e2)
         (qstx/rc (op #,(js-expand-expression #'e1 #f)
                      #,(js-expand-expression #'e2 #f)))])]
     [extract-js-expression
      (lambda (stx idmap)
        (syntax-parse stx
          [(op e1 e2)
           (hasheq
            'type "BinaryExpression"
            'operator (symbol->string (syntax->datum #'op))
            'left (extract-js-expression #'e1 idmap)
            'right (extract-js-expression #'e2 idmap))]))])))

(define-syntax + binop)
(define-syntax * binop)
(define-syntax - binop)
(define-syntax / binop)
(define-syntax < binop)
(define-syntax <= binop)
(define-syntax > binop)
(define-syntax >= binop)
(define-syntax == binop)

; Core statements

(define-syntax/generics (let x:id e)
  [(js-core-statement-pass1 ctx)   
   (qstx/rc (let #,(bind-var! ctx #'x) e))]
  [(js-core-statement-pass2)
   (qstx/rc (let x #,(js-expand-expression #'e #f)))]
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
   (def/stx m^ (bind! ctx #'m #'(generics [js-transformer e])))
   #'(let-syntax m^ e)]
  [(js-core-statement-pass2) this-syntax]
  [(extract-js-statement idmap)
   (hasheq 'type "EmptyStatement")])
   
(define-syntax/generics (return e)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (qstx/rc (return #,(js-expand-expression #'e #f)))]
  [(extract-js-statement idmap)
   (hasheq
    'type "ReturnStatement"
    'argument (extract-js-expression #'e idmap))])

(define-syntax/generics (while condition body ...)
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (qstx/rc (while #,(js-expand-expression #'condition #f)
                   #,@(expand-block #'(body ...) #f)))]
  [(extract-js-statement idmap)
   (hasheq
    'type "WhileStatement"
    'test (extract-js-expression #'condition idmap)
    'body (extract-block #'(body ...) idmap))])

(define-syntax/generics (if c (b1 ...) (b2 ...))
  [(js-core-statement-pass1 ctx) this-syntax]
  [(js-core-statement-pass2)
   (qstx/rc (if #,(js-expand-expression #'c #f)
                #,(expand-block #'(b1 ...) #f)
                #,(expand-block #'(b2 ...) #f)))]
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
     (with-disappeared-uses-and-bindings
         (def/stx expanded-js (js-expand-expression #'arg #f))
       (def/stx extracted (extract-js-expression #'expanded-js (make-idmap)))
       #'(begin
           (define wrapped (hash 'type "ExpressionStatement" 'expression 'extracted))
           ;(pretty-display wrapped)
           (runjs wrapped)))]))

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
  ; Thought this was broken due to expander bug, but doesn't seem to be...
  #;(js ((function ()
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

  ; Same as previous, but at statement rather than expression position.
  (js ((function ()
                 (let x 5)
                 (let-syntax m (lambda (stx)
                                 (syntax-parse stx
                                   [(_ arg)
                                    #'(return ((function (arg) (return x)) 6))])))
                 (inc! x)
                 (m x))))
  
  )
