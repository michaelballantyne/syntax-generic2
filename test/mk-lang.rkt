#lang racket

(require
  syntax-generic2/define
  (prefix-in mk: minikanren)
  racket/base
  (only-in racket/base [quote mk:quote] [#%app mk:app])
  (for-syntax
   racket/pretty
   racket/syntax
   syntax-generic2
   racket/base
   syntax/parse
   (only-in syntax/parse [define/syntax-parse def/stx])
   syntax/id-table
   ))

(provide define-relation relation run #%rkt-ref conj (rename-out [disj2 disj] [fresh exists])
         == #%term-datum #%lv-ref (rename-out [new-quote quote] [new-cons cons])
         absento symbolo numbero =/=
         fresh conde #%rel-app
         quasiquote unquote
         matche)

; term and goal nonterminals. To start we'll just have core forms.

(struct relation-value [proc])

(begin-for-syntax
  (define-syntax-generic core-term)
  (define-syntax-generic core-goal)
  (define-syntax-generic compile)
  (define-syntax-generic term-macro)
  (define-syntax-generic goal-macro)
  (define-syntax-generic relation-binding-argc)
  (define-syntax-generic relation-binding-proc)
  (define-syntax-generic logic-var-binding)
  (define-syntax-generic map-transform)

  (define (make-logic-var-binding)
    (generics
     ; Currently unreachable as there are no Racket subexpressions of mk goals
     [expand (λ (stx) (raise-syntax-error
                       #f "logic variables may only be used in miniKanren terms" stx))]
     [logic-var-binding (lambda (stx) stx)]))
  
  (define (bind-logic-var! sc name)
    (scope-bind! sc name #'(make-logic-var-binding)))

  (define (make-relation-binding proc n)
    (generics
     [expand (λ (stx) (raise-syntax-error
                       #f "relations may only be used in the context of a miniKanren goal" stx))]
     [relation-binding-argc (lambda (_) n)]
     [relation-binding-proc (lambda (_) proc)]))

  (define (expand-term stx sc)
    (syntax-parse stx
      [var:id
       #:when (logic-var-binding? #'var)
       (with-syntax ([#%lv-ref (datum->syntax stx '#%lv-ref)])
         (expand-term (qstx/rc (#%lv-ref var)) sc))]
      [var:id
       (with-syntax ([#%rkt-ref (datum->syntax stx '#%rkt-ref)])
         (expand-term (qstx/rc (#%rkt-ref var)) sc))]
      [(~or* l:number l:boolean)
       (with-syntax ([#%term-datum (datum->syntax stx '#%term-datum)])
         (expand-term (qstx/rc (#%term-datum l)) sc))]
      [_ #:when (core-term? stx sc)
         (apply-as-transformer core-term sc stx)]  ; dispatch to other core term forms
      [_ #:when (term-macro? stx sc)
         (expand-term (apply-as-transformer term-macro sc stx) sc)]
      [_ (raise-syntax-error #f "bad term syntax" stx)]))
  
  (define (expand-goal stx sc)
    (syntax-parse stx
      [_ #:when (core-goal? stx sc)
         (apply-as-transformer core-goal sc stx)]
      [_ #:when (goal-macro? stx sc)
         (expand-goal (apply-as-transformer goal-macro sc stx) sc)]
      [(n:id t ...) ; if n not bound as goal syntax, interpret as a relation application
       (with-syntax ([#%rel-app (datum->syntax stx '#%rel-app)])
         (expand-goal (qstx/rc (#%rel-app n t ...)) sc))]
      [_ (raise-syntax-error #f "bad goal syntax" stx)]))

  (define (dispatch-compile stx)
    (apply-as-transformer compile #f stx))

  #;(define relation-impl (make-free-id-table))

  (define (build-conj2 l)
    (when (null? l) (error 'build-conj2 "requires at least one item"))
    (let recur ([l (reverse l)])
      (if (= (length l) 1)
          (car l)
          #`(conj2
             #,(recur (cdr l))
             #,(car l)))))

  ; TODO: also account for =/=, symbolo, numbero, absento
  (define (reorder-conjunction stx)
    (define lvars '())
    (define unifications '())
    (define others '())
    (let recur ([stx stx])
      (syntax-parse stx #:literals (conj2 fresh1 ==)
        [(conj2 g1 g2) (recur #'g1) (recur #'g2)]
        [(fresh1 (x:id ...) g)
         (set! lvars (cons (syntax->list #'(x ...)) lvars))
         (recur #'g)]
        [(== t1 t2) (set! unifications (cons this-syntax unifications))]
        [_ (set! others (cons (reorder-conjunctions this-syntax) others))]))
    (let ([lvars (apply append (reverse lvars))]
          [body (build-conj2 (append (reverse unifications) (reverse others)))])
      (if (null? lvars)
          body
          #`(fresh1 #,lvars #,body))))
  
  (define (reorder-conjunctions stx)
    (define (maybe-reorder stx)
      (syntax-parse stx
        #:literals (conj2 fresh1)
        [((~or conj2 fresh1) . _) (reorder-conjunction this-syntax)]
        [_ this-syntax]))
    (map-transform stx maybe-reorder))

  (define (compile-goal stx sc)
    (define expanded (expand-goal stx sc))
    (define reordered (reorder-conjunctions expanded))
    (define compiled (dispatch-compile reordered))
    compiled)
  )

; run and define-relations are the interface with Racket

(define-syntax run-core
  (syntax-parser
    [(_ n:number (v:id ...) g)
     (with-disappeared-uses-and-bindings
      ; Expansion
      (define sc (make-expression-scope))
      (def/stx (v^ ...)
        (for/list ([v (syntax->list #'(v ...))])
          (bind-logic-var! sc v)))
      (def/stx g^ (compile-goal #'g sc))
      #'(mk:run n (v^ ...) g^))]))

(define-syntax relation
  (syntax-parser
    [(_ (v:id ...) g)
     (with-disappeared-uses-and-bindings
      ; Expand
      (define sc (make-expression-scope))
      (def/stx (v^ ...)
        (for/list ([v (syntax->list #'(v ...))])
          (bind-logic-var! sc v)))
      (def/stx g^ (compile-goal #'g sc))
      #'(relation-value
         (lambda (v^ ...)
           g^)))]))

(define-syntax define-relation
  (syntax-parser 
    [(_ (name:id v:id ...) g)
     #`(begin
         ; Bind static information for expansion
         (define-syntax name (make-relation-binding #'tmp #,(length (syntax->list #'(v ...)))))
         ; Binding for the the compiled function. Expansion of `relation` expands and compiles the
         ; body in the definition context's second pass.
         (define tmp (relation (v ...) g)))]))

; Term forms

(define-syntax/generics (#%lv-ref v)
  [(core-term)
   (unless (logic-var-binding? #'v)
     (raise-syntax-error #f "unbound logic variable" #'v))
   this-syntax]
  [(compile) #'v]
  [(map-transform f) (f this-syntax)])

(define (mk-value? v)
  (or (symbol? v)
      (number? v)
      (null? v)
      (and (pair? v)
           (mk-value? (car v))
           (mk-value? (cdr v)))))

(define-syntax/generics (#%rkt-ref v)
  [(core-term) this-syntax]
  [(compile) (syntax/loc #'v (invariant-assertion mk-value? v))]
  [(map-transform f) (f this-syntax)])

(define-syntax/generics (#%term-datum l:number)
  [(core-term) this-syntax]
  [(compile) #'(quote l)]
  [(map-transform f) (f this-syntax)])

(define-syntax/generics (new-quote d)
  [(core-term) this-syntax]
  [(compile) #'(quote d)]
  [(map-transform f) (f this-syntax)])

(define-syntax/generics (new-cons t1 t2)
  [(core-term)
   (def/stx t1^ (expand-term #'t1 #f))
   (def/stx t2^ (expand-term #'t2 #f))
   (qstx/rc (new-cons t1^ t2^))]
  [(compile)
   (def/stx t1^ (dispatch-compile #'t1))
   (def/stx t2^ (dispatch-compile #'t2))
   (qstx/rc (cons t1^ t2^))]
  [(map-transform f)
   (f (qstx/rc (new-cons #,(map-transform #'t1 f) #,(map-transform #'t2 f))))])

; Goal forms

(begin-for-syntax
  (define (binary-term runtime-op)
    (generics/parse (op t1 t2)
      [(core-goal)
       (def/stx t1^ (expand-term #'t1 #f))
       (def/stx t2^ (expand-term #'t2 #f))
       (qstx/rc (op t1^ t2^))]
      [(compile)
       (def/stx t1^ (dispatch-compile #'t1))
       (def/stx t2^ (dispatch-compile #'t2))
       #`(#,runtime-op t1^ t2^)]
      [(map-transform f)
       (f (qstx/rc (op #,(map-transform #'t1 f) #,(map-transform #'t2 f))))]))
  (define (unary-term runtime-op)
    (generics/parse (op t)
      [(core-goal)   
       (def/stx t^ (expand-term #'t #f))
       (qstx/rc (op t^))]
      [(compile)
       (def/stx t^ (dispatch-compile #'t))
       #`(#,runtime-op t^)]
      [(map-transform f)
       (f (qstx/rc (op #,(map-transform #'t f))))])))

(define-syntax == (binary-term #'mk:==))
(define-syntax =/= (binary-term #'mk:=/=))
(define-syntax absento (binary-term #'mk:absento))
(define-syntax symbolo (unary-term #'mk:symbolo))
(define-syntax numbero (unary-term #'mk:numbero))

(define-syntax/generics (#%rel-app n t ...)
  [(core-goal)
   ; Check relation is bound
   (unless (relation-binding-argc? #'n)
     (raise-syntax-error #f "unbound relation" #'n))
   
   ; Check argument count matches definition
   (let ([expected (relation-binding-argc #'n)]
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
  [(compile)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (dispatch-compile t)))
   (def/stx n^ (relation-binding-proc #'n))
   #'(#%app (relation-value-proc n^) t^ ...)]
  [(map-transform f)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (map-transform t f)))
   (f (qstx/rc (#%rel-app n t^ ...)))])

(define-syntax/generics (apply-relation e t ...)
  [(core-goal)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (expand-term t #f)))
   (qstx/rc (apply-relation e t^ ...))]
  [(compile)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (dispatch-compile t)))
   (def/stx e^ (syntax/loc #'e (invariant-assertion relation-value? e)))
   #'(#%app (relation-value-proc e^) t^ ...)]
  [(map-transform f)
   (def/stx (t^ ...)
     (for/list ([t (syntax->list #'(t ...))])
       (map-transform t f)))
   (f (qstx/rc (apply-relation e t^ ...)))])

(provide apply-relation)

(define-syntax/generics (disj2 g1 g2)
  [(core-goal)
   (def/stx g1^ (expand-goal #'g1 #f))
   (def/stx g2^ (expand-goal #'g2 #f))
   (qstx/rc (disj2 g1^ g2^))]
  [(compile)
   (def/stx g1^ (dispatch-compile #'g1))
   (def/stx g2^ (dispatch-compile #'g2))
   #'(mk:conde [g1^] [g2^])]
  [(map-transform f)
   (f (qstx/rc (disj2 #,(map-transform #'g1 f) #,(map-transform #'g2 f))))])

(define-syntax/generics (conj2 g1 g2)
  [(core-goal)
   (def/stx g1^ (expand-goal #'g1 #f))
   (def/stx g2^ (expand-goal #'g2 #f))
   (qstx/rc (conj2 g1^ g2^))]
  [(compile)
   (def/stx g1^ (dispatch-compile #'g1))
   (def/stx g2^ (dispatch-compile #'g2))
   #'(mk:fresh () g1^ g2^)]
  [(map-transform f)
   (f (qstx/rc (conj2 #,(map-transform #'g1 f) #,(map-transform #'g2 f))))])

(define-syntax/generics (fresh1 (x:id ...) g)
  [(core-goal)
   (define sc (make-expression-scope))
   (def/stx (x^ ...)
     (for/list ([x (syntax->list #'(x ...))])
       (bind-logic-var! sc x)))
   (def/stx g^ (expand-goal #'g sc))
   (qstx/rc (fresh1 (x^ ...) g^))]
  [(compile)
   (def/stx g^ (dispatch-compile #'g))
   #'(mk:fresh (x ...) g^)]
  [(map-transform f)
   (f (qstx/rc (fresh1 (x ...) #,(map-transform #'g f))))])

; Syntactic sugar

(define-syntax run
  (syntax-parser
    [(_ n:number (v:id ...) g g* ...)
     #'(run-core n (v ...) (conj g g* ...))]))

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
    [(fresh () g1 g* ...)
     #'(conj g1 g* ...)]
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
     (let recur ([stx #'q])
       (syntax-parse stx #:datum-literals (unquote)
         [(unquote e) #'e]
         [(unquote . rest)
          (raise-syntax-error 'unquote "bad unquote syntax" stx)]
         [(a . d) #`(new-cons #,(recur #'a) #,(recur #'d))]
         [(~or* v:identifier v:number) #'(new-quote v)]
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
                   body)))))]
      [(matche v (pat g ...) ...)
       #'(matche (v) ([pat] g ...) ...)])))

; Next step: structures and algebraic data types. May want to leave s-expressions in as a built-in
; type to allow interpreters that want to accept s-expression syntax or produce s-expression values.
;
;  SExp = (ListOf SExp)
;       | number
;       | string
;       | symbol
