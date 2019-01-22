#lang racket/base

(require "mk-lang.rkt")
;(require minikanren)
;(define-syntax-rule (define-relation (n v ...) g) (define (n v ...) g))

#;(define-relation (appendo l1 l2 l3)
  (conde
   [(== l1 '()) (== l3 l2)]  ; base case
   [(fresh (head rest result) ; recursive case
      (== `(,head . ,rest) l1)
      (== `(,head . ,result) l3)
      (appendo rest l2 result))]))

(define-relation (appendo l1 l2 l3)
  (matche [l1 l3]
    [[() ,_] (== l3 l2)]
    [[(,head . ,rest) (,head . ,result)] (appendo rest l2 result)]))

(define-relation (eval-expo exp env val)
  (conde
   ((fresh (v)
      (== `(quote ,v) exp)
      (not-in-envo 'quote env)
      (absento 'closure v)
      (== v val)))
   ((fresh (a*)
      (== `(list . ,a*) exp)
      (not-in-envo 'list env)
      (absento 'closure a*)
      (proper-listo a* env val)))
   ((symbolo exp) (lookupo exp env val))
   ((fresh (rator rand x body env^ a)
      (== `(,rator ,rand) exp)
      (eval-expo rator env `(closure ,x ,body ,env^))
      (eval-expo rand env a)
      (eval-expo body `((,x . ,a) . ,env^) val)))
   ((fresh (x body)
      (== `(lambda (,x) ,body) exp)
      (symbolo x)
      (not-in-envo 'lambda env)
      (== `(closure ,x ,body ,env) val)))))

(define-relation (not-in-envo x env)
  (conde
   ((fresh (y v rest)
      (== `((,y . ,v) . ,rest) env)
      (=/= y x)
      (not-in-envo x rest)))
   ((== '() env))))

(define-relation (proper-listo exp env val)
  (conde
   ((== '() exp)
    (== '() val))
   ((fresh (a d t-a t-d)
      (== `(,a . ,d) exp)
      (== `(,t-a . ,t-d) val)
      (eval-expo a env t-a)
      (proper-listo d env t-d)))))

(define-relation (lookupo x env t)
  (fresh (rest y v)
    (== `((,y . ,v) . ,rest) env)
    (conde
     ((== y x) (== v t))
     ((=/= y x) (lookupo x rest t)))))

(run 1 (q) (appendo '(a b) '(c) q))

(run 10 (q) (eval-expo q '() q))