#lang racket/base

(require "mk-lang.rkt")

(define-relation (appendo l1 l2 l3)
  (conde
   [(== l1 '()) (== l3 l2)]  ; base case
   [(fresh (head rest result) ; recursive case
      (== `(,head . ,rest) l1)
      (== `(,head . ,result) l3)
      (appendo rest l2 result))]))

(run 1 (q) (appendo '(a b) '(c) q))