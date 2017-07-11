#lang mf-apply racket/base

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

;; =============================================================================

(define-language Λ
  [M ::= ;; terms
         ;; 'let' is for polymorphism, so restricted to values
         x V (M M) (let (x V) M) (M @ l)]
  [V ::= b ((λ x M) @ t)]
  [b ::= true false]
  [E ::= ;; evaluation context
         hole (E M) (V E) (E @ l)]
  [x* ::= (x ...)]
  [t l x ::= ;; l = expression label
             ;; t = function tag
             ;; x = program variable
             variable-not-otherwise-mentioned]
  #:binding-forms
    (λ x M #:refers-to x)
    (let (x V) M #:refers-to x))
;; programs are closed terms, Λ0

(define M? (redex-match? Λ M))
(define V? (redex-match? Λ V))
(define b? (redex-match? Λ b))

(define (Λ=? t0 t1)
  (alpha-equivalent? Λ t0 t1))

(define-metafunction Λ
  tag->function : t M -> any
  [(tag->function t x)
   #f]
  [(tag->function t b)
   #f]
  [(tag->function t ((λ x M) @ t))
   (λ x M)]
  [(tag->function t ((λ x M) @ t_1))
   #{tag->function t M}]
  [(tag->function t (M_0 M_1))
   ,(or (term #{tag->function t M_0})
        (term #{tag->function t M_1}))]
  [(tag->function t (let (x V) M))
   ,(or (term #{tag->function t V})
        (term #{tag->function t M}))]
  [(tag->function t (M @ l))
   #{tag->function t M}])

(module+ test
  (test-case "tag->function"
    (let ([my-tag (term t0)])
      (check-true* (λ (t u) (Λ=? (term #{tag->function ,my-tag ,t}) u))
       [(term true)
        #f]
       [(term y)
        #f]
       [(term ((λ x x) @ ,my-tag))
        (term (λ x x))]
       [(term ((λ x ((λ y true) @ ,my-tag)) @ t1))
        (term (λ y true))]
       [(term (((λ x true) @ ,my-tag) ((λ y false) @ t1)))
        (term (λ x true))]
       [(term (((λ x true) @ t1) ((λ y false) @ ,my-tag)))
        (term (λ x false))]
       [(term (let (z ((λ x true) @ ,my-tag)) ((λ y false) @ t2)))
        (term (λ x true))]
       [(term (let (z ((λ x true) @ t1)) ((λ y false) @ ,my-tag)))
        (term (λ x false))]
       #;[(term (((λ x true) @ ,my-tag) @ t2))
        (term (λ x true))]))
))

(define-judgment-form Λ
  #:mode (free-variables I O)
  #:contract (free-variables M x*)
  [
   --- Var
   (free-variables x (x))]
  [
   (free-variables M x*_2)
   (where x*_1 ,(set-remove (term x*_2) (term x)))
   --- Lambda
   (free-variables ((λ x M) @ t) x*_1)]
  [
   --- Base
   (free-variables b ())]
  [
   (free-variables M_0 x*_0)
   (free-variables M_1 x*_1)
   (where x*_2 ,(set-union (term x*_0) (term x*_1)))
   --- App
   (free-variables (M_0 M_1) x*_2)]
  [
   (free-variables V x*_0)
   (free-variables M x*_1)
   (where x*_2 ,(set-union (term x*_0) (set-remove (term x*_1) (term x))))
   --- Let
   (free-variables (let (x V) M) x*_2)]
  [
   (free-variables M x*_1)
   --- Ann
   (free-variables (M @ l) x*_1)])

(define-metafunction Λ
  free-variables# : M -> x*
  [(free-variables# M)
   x*
   (judgment-holds (free-variables M x*))]
  [(free-variables# M)
   ,(raise-user-error 'free-variables "undefined for ~a" (term M))])

(define-judgment-form Λ
  #:mode (closed I)
  #:contract (closed M)
  [
   (free-variables M ())
   ---
   (closed M)])

(module+ test
  (test-case "free-variables"
    (check-apply* (λ (t) (term #{free-variables# ,t}))
     [(term x)
      ==> (term (x))]
     [(term true)
      ==> (term ())]
     [(term ((λ x x) @ t0))
      ==> (term ())]
     [(term ((λ x y) @ t1))
      ==> (term (y))]
     [(term (((λ x y) @ t1) ((λ x z) @ t3)))
      ==> (term (z y))]
     [(term (((λ x y) @ t1) ((λ x y) @ t3)))
      ==> (term (y))]
     [(term (let (x ((λ z y) @ t0)) z))
      ==> (term (z y))])
  )
  (test-case "closed"
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term x)
      ==> #f]
     [(term ((λ x y) @ t7))
      ==> #f]
     [(term (((λ x y) @ t0) true))
      ==> #f]
     [(term (true ((λ x y) @ t0)))
      ==> #f]
     [(term (let (x ((λ z y) @ t6)) x))
      ==> #f]
     [(term (let (x true) y))
      ==> #f])
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term false)
      ==> #t]
     [(term ((λ x true) @ t0))
      ==> #t]
     [(term (((λ x x) @ t0) ((λ x x) @ t0)))
      ==> #t]
     [(term (let (x true) x))
      ==> #t]))
)

(define --->
  (reduction-relation Λ
   #:domain M
   [--> (in-hole E (((λ x M) @ t) V))
        (in-hole E (substitute M x V))
        βv]
   [--> (in-hole E (let (x V) M))
        (in-hole E (substitute M x V))
        βlet]
   [--> (in-hole E (V @ l))
        (in-hole E V)
        unlabel]))

(define (--->* t)
  (define v* (apply-reduction-relation* ---> t))
  (cond
   [(null? v*)
    (raise-user-error '--->* "no result for ~a" t)]
   [(null? (cdr v*))
    (car v*)]
   [else
    (raise-user-error '--->* "multiple results ~a --->* ~a" t v*)]))

(define-metafunction Λ
  eval : M -> V
  [(eval M)
   ,(--->* (term M))
   (judgment-holds (closed M))]
  [(eval M)
   ,(raise-user-error 'eval "undefined for open term ~a, free variables are ~a" (term M) (term x*))
   (where x* #{free-variables# M})])

(module+ test
  (check-true* (λ (t u) (Λ=? (term #{eval ,t}) u))
   [(term true)
    (term true)]
   [(term ((λ x true) @ t0))
    (term ((λ x true) @ t0))]
   [(term (((λ x true) @ t0) false))
    (term true)]
   [(term (((λ x x) @ t1) true))
    (term true)]
   [(term ((((λ x x) @ t1) true) @ l2))
    (term true)]
   [(term (let (x ((λ y y) @ t0)) (x false)))
    (term false)]))

;; TODO constraint language
