#lang mf-apply racket/base

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

(define *debug* (make-parameter #f))
(define (debug msg . arg*)
  (when (*debug*) (printf "[DEBUG] ") (apply printf msg arg*) (newline)))

;; =============================================================================

(define-language PureScheme
  [e ::= v
         (ap e e)
         (if e e e)
         (let ([x e]) e)
         (CHECK-ap e e)
         (cons e e)]
  [v ::= c x (λ (x) e) (cons v v)]
  [c ::= basic-constant unchecked-prim checked-prim]
  [basic-constant ::= integer boolean null]
  [unchecked-prim ::= add1 car cdr cons]
  [checked-prim ::= CHECK-add1 CHECK-car CHECK-cdr]
  [a ::= v CHECK]
  [error ::= UNDEFINED]

  [x* ::= (x ...)]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let ([x e_0]) e_1 #:refers-to x))

;; Programs are closed expressions

(define e? (redex-match? PureScheme e))
(define v? (redex-match? PureScheme v))
(define c? (redex-match? PureScheme c))

(define (PureScheme=? t0 t1)
  (alpha-equivalent? PureScheme t0 t1))

(module+ test

  (test-case "redex-match"
    (check-pred e? (term #t))
    (check-pred e? (term (let ([x 4]) x)))
    (check-pred e? (term (let ([x (CHECK-ap f g)]) (CHECK-ap h x))))
    (check-pred e? (term (λ (x) x)))
    (check-pred e? (term (ap car (cons 1 null))))

    (check-pred c? (term add1))
    (check-pred c? (term 42))

    (check-pred v? (term #t))
    (check-pred v? (term (λ (x) x)))
    (check-pred v? (term (cons 1 null)))

    (void))
)

(define-judgment-form PureScheme
  #:mode (free-variables I O)
  #:contract (free-variables e x*)
  [
   --- Var
   (free-variables x (x))]
  [
   (free-variables e x*_2)
   (where x*_1 ,(set-remove (term x*_2) (term x)))
   --- Lambda
   (free-variables (λ (x) e) x*_1)]
  [
   --- Const
   (free-variables c ())]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x*_2 ,(set-union (term x*_0) (term x*_1)))
   --- CHECK-ap
   (free-variables (CHECK-ap e_0 e_1) x*_2)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x*_2 ,(set-union (term x*_0) (term x*_1)))
   --- ap
   (free-variables (ap e_0 e_1) x*_2)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (free-variables e_2 x*_2)
   (where x* ,(set-union (term x*_0) (term x*_1) (term x*_2)))
   --- if
   (free-variables (if e_0 e_1 e_2) x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x* ,(set-union (term x*_0) (set-remove (term x*_1) (term x))))
   --- let
   (free-variables (let ([x e_0]) e_1) x*)])

(define-metafunction PureScheme
  free-variables# : e -> x*
  [(free-variables# e)
   x*
   (judgment-holds (free-variables e x*))]
  [(free-variables# e)
   ,(raise-user-error 'free-variables "undefined for ~a" (term e))])

(define-judgment-form PureScheme
  #:mode (closed I)
  #:contract (closed e)
  [
   (free-variables e ())
   ---
   (closed e)])

(module+ test
  (test-case "free-variables"
    (check-apply* (λ (t) (term #{free-variables# ,t}))
     [(term x)
      ==> (term (x))]
     [(term #t)
      ==> (term ())]
     [(term (λ (x) x))
      ==> (term ())]
     [(term (λ (x) y))
      ==> (term (y))]
     [(term (CHECK-ap (λ (x) y) (λ (x) z)))
      ==> (term (z y))]
     [(term (CHECK-ap (λ (x) y) (λ (x) y)))
      ==> (term (y))]
     [(term (let ([a 1]) b))
      ==> (term (b))]
     [(term (let ([a 1]) a))
      ==> (term ())]
     [(term (let ([a a]) a))
      ==> (term (a))]
     [(term (let ([a b]) a))
      ==> (term (b))])
  )
  (test-case "closed"
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term x)
      ==> #f]
     [(term (λ (x) y))
      ==> #f]
     [(term (CHECK-ap (λ (x) y) #true))
      ==> #f]
     [(term (CHECK-ap TRUE (λ (x) y)))
      ==> #f])
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term #false)
      ==> #t]
     [(term (λ (x) #true))
      ==> #t]
     [(term (CHECK-ap (λ (x) x) (λ (x) x)))
      ==> #t]
     [(term (let ([x x]) x))
      ==> #f]))
)

(define-metafunction PureScheme
  δ : c v -> any
  [(δ CHECK-add1 integer)
   ,(+ 1 (term integer))]
  [(δ CHECK-add1 v)
   CHECK]
  [(δ add1 integer)
   ,(+ 1 (term integer))]
  [(δ CHECK-car (cons v_0 v_1))
   v_0]
  [(δ CHECK-car v)
   CHECK]
  [(δ car (cons v_0 v_1))
   v_0]
  [(δ CHECK-cdr (cons v_0 v_1))
   v_1]
  [(δ CHECK-cdr v)
   CHECK]
  [(δ cdr (cons v_0 v_1))
   v_1]
  [(δ c v)
   UNDEFINED])

(module+ test
  (test-case "δ"
    (check-equal? (term #{δ add1 5}) (term 6))
    (check-equal? (term #{δ CHECK-add1 5}) (term 6))
    (check-equal? (term #{δ car (cons 1 null)}) (term 1))
    (check-equal? (term #{δ CHECK-car (cons 1 null)}) (term 1))
    (check-equal? (term #{δ cdr (cons 1 null)}) (term null))
    (check-equal? (term #{δ CHECK-cdr (cons 1 null)}) (term null))
    (check-equal? (term #{δ CHECK-cdr null}) (term CHECK))
    (check-equal? (term #{δ cdr null}) (term UNDEFINED))))

(define-judgment-form PureScheme
  #:mode (meaningful I)
  #:contract (meaningful e)
  [
   --- CHECK-ap
   (meaningful (CHECK-ap e v))]
  [
   --- ap-checked
   (meaningful (ap checked-prim v))]
  [
   (where v_1 #{δ unchecked-prim v})
   --- ap-unchecked
   (meaningful (ap unchecked-prim v))]
  [
   --- ap-λ
   (meaningful (ap (λ (x) e) v))])

(define-metafunction PureScheme
  meaningless? : e -> boolean
  [(meaningless? e)
   #false
   (judgment-holds (meaningful e))]
  [(meaningless? e)
   #true])

(module+ test
  (test-case "meaningless"
    (check-true* (λ (t) (term #{meaningless? ,t}))
      [(term (ap add1 #true))]
      [(term (ap car null))]
      [(term (ap 1 2))])))

