#lang racket/base

(module t typed/racket/base
  (provide f)

  (: f (-> String String))
  (define (f x) x))

(module u racket/base
  (require (submod ".." f))
  (f "hello"))
