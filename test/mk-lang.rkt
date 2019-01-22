#lang racket

(require
  syntax-generic2/define
  (prefix-in mk: minikanren)
  (rename-in racket/base [quote mk:quote] [#%app mk:app])
  (for-syntax
   racket/syntax
   syntax-generic2
   racket/base
   (rename-in syntax/parse [define/syntax-parse def/stx])
   syntax/id-table
   ))

(provide define-relation run
         == #%term-datum #%lv-ref (rename-out [new-quote quote] [new-cons cons])
         absento symbolo numbero =/=
         fresh conde #%rel-app
         quasiquote unquote
         matche)

; term and goal nonterminals. To start we'll just have core forms.

(begin-for-syntax
  (define-syntax-generic core-term)
  (define-syntax-generic core-goal)
  (define-syntax-generic core-term-compile)
  (define-syntax-generic core-goal-compile)
  (define-syntax-generic term-macro)
  (define-syntax-generic goal-macro)
  (define-syntax-generic relation-binding)
  (define-syntax-generic logic-var-binding)

  (define logic-var-binding-instance
    (generics
     [logic-var-binding (lambda (stx) stx)]))
  
  (define (bind-logic-var! sc name)
    (scope-bind! sc name #'logic-var-binding-instance))

  (define (expand-term stx sc)
    (syntax-parse stx
      [var:id
       (with-syntax ([#%lv-ref (datum->syntax stx '#%lv-ref)])
         (expand-term (qstx/rc (#%lv-ref var)) sc))]
      [(~or* l:number l:boolean)
       (with-syntax ([#%term-datum (datum->syntax stx '#%term-datum)])
         (expand-term (qstx/rc (#%term-datum l)) sc))]
      [_
       #:when (core-term? stx sc)
       (apply-as-transformer core-term sc stx)]  ; dispatch to other core term forms
      [_
       #:when (term-macro? stx sc)
       (expand-term (apply-as-transformer term-macro sc stx) sc)]
      [_
       (raise-syntax-error #f "bad term syntax" stx)]))
  (define (expand-goal stx sc)
    (syntax-parse stx
      [_
       #:when (core-goal? stx sc)
       (apply-as-transformer core-goal sc stx)]
      [_
       #:when (goal-macro? stx sc)
       (expand-goal (apply-as-transformer goal-macro sc stx) sc)]
      [(n:id t ...) ; if n not bound as goal syntax, interpret as a relation application
       (with-syntax ([#%rel-app (datum->syntax stx '#%rel-app)])
         (expand-goal (qstx/rc (#%rel-app n t ...)) sc))]
      [_
       (raise-syntax-error #f "bad goal syntax" stx)]))

  (define (compile-term stx)
    (apply-as-transformer core-term-compile #f stx))
  (define (compile-goal stx)
    (apply-as-transformer core-goal-compile #f stx))

  (define relation-impl (make-free-id-table))
  
  )

; run and define-relations are the interface with Racket

(define-syntax run
  (syntax-parser
    [(_ n:number (v:id ...) g)
     (with-disappeared-uses-and-bindings
      ; Expansion
      (define sc (make-expression-scope))
      (def/stx (v^ ...)
        (for/list ([v (syntax->list #'(v ...))])
          (bind-logic-var! sc v)))
      (def/stx g^ (expand-goal #'g sc))

      (def/stx g^^ (compile-goal #'g^))
      #'(mk:run n (v^ ...) g^^))]))

(define-syntax relation
  (syntax-parser
    [(_ (v:id ...) g)
     (with-disappeared-uses-and-bindings
      ; Expand
      (define sc (make-expression-scope))
      (def/stx (v^ ...)
        (for/list ([v (syntax->list #'(v ...))])
          (bind-logic-var! sc v)))
      (def/stx g^ (expand-goal #'g sc))

      ; Compile
      (def/stx g^^ (compile-goal #'g^))
      #'(lambda (v^ ...)
          g^^))]))

(begin-for-syntax
  (define (relation-binding-instance n)
    (generics
     [relation-binding (lambda (_) n)])))

(define-syntax define-relation
  (syntax-parser 
    [(_ (name:id v:id ...) g)
     #`(begin
         ; Bind static information for expansion
         (define-syntax name (relation-binding-instance #,(length (syntax->list #'(v ...)))))
         ; Create mapping from source relation name to compiled function name
         (begin-for-syntax
           (free-id-table-set! relation-impl #'name #'tmp))
         ; Binding for the the compiled function. Expansion of `relation` expands and compiles the
         ; body in the definition context's second pass.
         (define tmp (relation (v ...) g)))]))

; Term forms

(define-syntax/generics (#%lv-ref v)
  [(core-term)
   (unless (logic-var-binding? #'v)
     (raise-syntax-error #f "unbound logic variable" #'v))
   this-syntax]
  [(core-term-compile)
   #'v])

(define-syntax/generics (#%term-datum l:number)
  [(core-term)
   this-syntax]
  [(core-term-compile)
   #'(quote l)])

(define-syntax/generics (new-quote d)
  [(core-term)
   this-syntax]
  [(core-term-compile)
   #'(quote d)])

(define-syntax/generics (new-cons t1 t2)
  [(core-term)
   (def/stx t1^ (expand-term #'t1 #f))
   (def/stx t2^ (expand-term #'t2 #f))
   #'(new-cons t1^ t2^)]
  [(core-term-compile)
   (def/stx t1^ (compile-term #'t1))
   (def/stx t2^ (compile-term #'t2))
   #'(cons t1^ t2^)])

; Goal forms

(define-syntax/generics (== t1 t2)
  [(core-goal)
   (def/stx t1^ (expand-term #'t1 #f))
   (def/stx t2^ (expand-term #'t2 #f))
   (qstx/rc (== t1^ t2^))]
  [(core-goal-compile)
   (def/stx t1^ (compile-term #'t1))
   (def/stx t2^ (compile-term #'t2))
   #'(mk:== t1^ t2^)])

(define-syntax/generics (=/= t1 t2)
  [(core-goal)
   (def/stx t1^ (expand-term #'t1 #f))
   (def/stx t2^ (expand-term #'t2 #f))
   (qstx/rc (=/= t1^ t2^))]
  [(core-goal-compile)
   (def/stx t1^ (compile-term #'t1))
   (def/stx t2^ (compile-term #'t2))
   #'(mk:=/= t1^ t2^)])

(define-syntax/generics (symbolo t)
  [(core-goal)
   (def/stx t^ (expand-term #'t #f))
   (qstx/rc (symbolo t^))]
  [(core-goal-compile)
   (def/stx t^ (compile-term #'t))
   #'(mk:symbolo t^)])

(define-syntax/generics (numbero t)
  [(core-goal)
   (def/stx t^ (expand-term #'t #f))
   (qstx/rc (numbero t^))]
  [(core-goal-compile)
   (def/stx t^ (compile-term #'t))
   #'(mk:numbero t^)])

(define-syntax/generics (absento ((~literal new-quote) (~and v (~or* () _:number :identifier))) t)
  [(core-goal)
   (def/stx t^ (expand-term #'t #f))
   (qstx/rc (absento (new-quote v) t^))]
  [(core-goal-compile)
   (def/stx t^ (compile-term #'t))
   #'(mk:absento (quote v) t^)])

(define-syntax/generics (#%rel-app n t ...)
  [(core-goal)
   ; Check relation is bound
   (unless (relation-binding? #'n)
     (raise-syntax-error #f "unbound relation" #'n))
   
   ; Check argument count matches definition
   (let ([expected (relation-binding #'n)]
         [actual (length (syntax->list #'(t ...)))])
     (unless (= expected actual)
       (raise-syntax-error
        (syntax-e #'n)
        (format "wrong number of arguments to relation. Expected ~a; Given ~a" expected actual)
        this-syntax)))
   
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (expand-term t #f)))
   (qstx/rc (#%rel-app n t^ ...))]
  [(core-goal-compile)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (compile-term t)))
   (def/stx n^ (free-id-table-ref relation-impl #'n))
   #'(#%app n^ t^ ...)])

(define-syntax/generics (disj2 g1 g2)
  [(core-goal)
   (def/stx g1^ (expand-goal #'g1 #f))
   (def/stx g2^ (expand-goal #'g2 #f))
   (qstx/rc (disj2 g1^ g2^))]
  [(core-goal-compile)
   (def/stx g1^ (compile-goal #'g1))
   (def/stx g2^ (compile-goal #'g2))
   #'(mk:conde [g1^] [g2^])])

(define-syntax/generics (conj2 g1 g2)
  [(core-goal)
   (def/stx g1^ (expand-goal #'g1 #f))
   (def/stx g2^ (expand-goal #'g2 #f))
   (qstx/rc (conj2 g1^ g2^))]
  [(core-goal-compile)
   (def/stx g1^ (compile-goal #'g1))
   (def/stx g2^ (compile-goal #'g2))
   #'(mk:fresh () g1^ g2^)])

(define-syntax/generics (fresh1 (x:id ...) g)
  [(core-goal)
   (define sc (make-expression-scope))
   (def/stx (x^ ...)
     (for/list ([x (syntax->list #'(x ...))])
       (bind-logic-var! sc x)))
   (def/stx g^ (expand-goal #'g sc))
   (qstx/rc (fresh1 (x^ ...) g^))]
  [(core-goal-compile)
   (def/stx g^ (compile-goal #'g))
   #'(mk:fresh (x ...) g^)])

(define-syntax-rule
  (define-goal-macro m f)
  (define-syntax m (generics [goal-macro f])))

(define-syntax-rule
  (define-term-macro m f)
  (define-syntax m (generics [term-macro f])))

(define-goal-macro conj
  (syntax-parser
    [(conj g) #'g]
    [(conj g1 g2 g* ...) #'(conj (conj2 g1 g2) g* ...)]))

(define-goal-macro fresh
  (syntax-parser
    [(fresh (x:id ...)
       g1 g* ...)
     #'(fresh1 (x ...)
               (conj g1 g* ...))]))

(define-goal-macro conde
  (syntax-parser
    [(conde [g1 g1* ...])
     #'(conj g1 g1* ...)]
    [(conde [g1 g1* ...] [g g* ...] ...)
     #'(disj2
        (conj g1 g1* ...)
        (conde [g g* ...] ...))]))

(define-term-macro unquote
  (lambda (stx)
    (raise-syntax-error 'unquote "only valid within quasiquote" stx)))

(define-term-macro quasiquote
  (syntax-parser 
    [(_ q)
     (let rec ([stx #'q])
       (syntax-parse stx
         #:literals (unquote)
         [(unquote e)
          #'e]
         [(unquote . rest)
          (raise-syntax-error 'unquote "bad unquote syntax" stx)]
         [(a . d)
          #`(new-cons #,(rec #'a) #,(rec #'d))]
         [(~or* v:identifier v:number)
          #'(new-quote v)]
         [() #'(new-quote ())]))]))

(define-goal-macro matche
  (lambda (stx)    
    (syntax-case stx ()
      [(matche (v ...) ([pat ...] g ...) ...)
       (let ()
         (define remove-duplicates
           (lambda (ls eq-pred)
             (cond
               [(null? ls) '()]
               [(memf (lambda (x) (eq-pred (car ls) x)) (cdr ls))
                (remove-duplicates (cdr ls) eq-pred)]
               [else (cons (car ls) (remove-duplicates (cdr ls) eq-pred))])))
         (define parse-pattern
           (lambda (args pat)
             (syntax-case #`(#,args #,pat) ()
               [(() ()) #'(() () ())]
               [((a args ...) [p pat ...])
                (with-syntax ([(p^ (c ...) (x ...))
                               (parse-patterns-for-arg #'a #'p)])
                  (with-syntax ([([pat^ ...] (c^ ...) (x^ ...))
                                 (parse-pattern #'(args ...) #'[pat ...])])
                    #'([p^ pat^ ...] (c ... c^ ...) (x ... x^ ...))))]
               [x (error 'parse-pattern "bad syntax ~s ~s" args pat)])))
         (define parse-patterns-for-arg
           (lambda (v pat)
             (define loop
               (lambda (pat)
                 (syntax-case pat (unquote ?? ?) ; ?? is the new _, since _ isn't legal in R6
                   [(unquote ??)
                    (with-syntax ([_new (generate-temporary #'?_)])
                      #'((unquote _new) () (_new)))]
                   [(unquote x)
                    (when (free-identifier=? #'x v)
                      (error 'matche "argument ~s appears in pattern at an invalid depth"
                             (syntax->datum #'x)))
                    #'((unquote x) () (x))]
                   [(unquote (? c x))
                    (when (free-identifier=? #'x v)
                      (error 'matche "argument ~s appears in pattern at an invalid depth"
                             (syntax->datum #'x)))
                    #'((unquote x) ((c x)) (x))]
                   [(a . d)
                    (with-syntax ([((pat1 (c1 ...) (x1 ...))
                                    (pat2 (c2 ...) (x2 ...)))
                                   (map loop (syntax->list #'(a d)))])
                      #'((pat1 . pat2) (c1 ... c2 ...) (x1 ... x2 ...)))]
                   [x #'(x () ())])))
             (syntax-case pat (unquote ?)
               [(unquote u)
                (cond
                  [(and (identifier? #'u)
                        (free-identifier=? v #'u))
                   #'((unquote u) () ())]
                  [else (loop pat)])]
               [(unquote (? c u))
                (cond
                  [(and (identifier? #'u)
                        (free-identifier=? v #'u))
                   #'((unquote u) ((c x)) ())]
                  [else (loop pat)])]
               [else (loop pat)])))
         (unless
             (andmap (lambda (y) (= (length (syntax->datum #'(v ...))) (length y)))
                     (syntax->datum #'([pat ...] ...)))
           (error 'matche "pattern wrong length blah"))
         (with-syntax ([(([pat^ ...] (c ...) (x ...)) ...)
                        (map (lambda (y) (parse-pattern #'(v ...) y))
                             (syntax->list #'([pat ...] ...)))])
           (with-syntax ([((x^ ...) ...)
                          (map (lambda (ls)
                                 (remove-duplicates (syntax->list ls) free-identifier=?))
                               (syntax->list #'((x ...) ...)))])
             (with-syntax ([body
                            #'(conde
                                [(fresh (x^ ...) c ... (== `[pat^ ...] ls) g ...)]
                                ...)])
               #'(fresh (ls)
                   (== ls `(,v ...))
                   body)
               #;#'(let ([ls (list v ...)]) body)))))]
      [(matche v (pat g ...) ...)
       #'(matche (v) ([pat] g ...) ...)])))

; Next step: structures and algebraic data types. May want to leave s-expressions in as a built-in
; type to allow interpreters that want to accept s-expression syntax or produce s-expression values.
;
;  SExp = (ListOf SExp)
;       | number
;       | string
;       | symbol
