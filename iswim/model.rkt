#lang racket
(require redex/reduction-semantics)

(define-language iswim
  [M N L K ::= X (λ X M) (M M) b (o2 M M) (o1 M)]
  [o ::= o1 o2]
  [o1 ::= add1 sub1 issero subzero]
  [o2 ::= + - * ↑]
  [b ::= number]
  [V U W ::= b X (λ X M)]
  [E ::= hole (V E) (E M) (o V ... E M ...)]
  [X Y Z ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ X M #:refers-to X))


