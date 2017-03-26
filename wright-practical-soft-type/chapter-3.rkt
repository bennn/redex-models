#lang mf-apply racket/base

(require
  "../utils.rkt"
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
  [E ::= hole
         (ap E e) (ap v E)
         (if E e e)
         (let ([x E]) e)
         (CHECK-ap E e) (CHECK-ap v E)
         (cons E e) (cons v E)]
  [c ::= basic-constant Prim]
  [Prim ::= unchecked-prim checked-prim]
  [basic-constant ::= integer boolean nil]
  [unchecked-prim ::= add1 car cdr cons]
  [checked-prim ::= check-add1 check-car check-cdr]
  [a ::= v check]
  [error ::= UNDEFINED]
  ;; --- 3.4
  [σ τ ::= ;; static types
           slack
           (U partition ... slack)
           (μ α τ)]
  [partition ::= (k flag σ ...)]
  [slack ::= ∅ α]
  [k ::= ;; tags, partition the data domain
         True
         False
         Num
         Nil
         Cons
         →]
  [flag ::= ++ -- φ]
  ;; ---
  [k* ::= (k ...)]
  [σ* ::= (σ ...)]
  [τ* ::= (τ ...)]
  [x* ::= (x ...)]
  [x α φ ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let ([x e_0]) e_1 #:refers-to x))

;; Programs are closed expressions

(define e? (redex-match? PureScheme e))
(define v? (redex-match? PureScheme v))
(define a? (redex-match? PureScheme a))
(define c? (redex-match? PureScheme c))
(define τ? (redex-match? PureScheme τ))
(define σ? τ?)
(define partition? (redex-match? PureScheme partition))
(define flag? (redex-match? PureScheme flag))
(define k? (redex-match? PureScheme k))
(define Prim? (redex-match? PureScheme Prim))

(define (check? x)
  (equal? x (term check)))

(define (stuck? x)
  (equal? x (term STUCK)))

(define (PureScheme=? t0 t1)
  (alpha-equivalent? PureScheme t0 t1))

(module+ test

  (test-case "redex-match"
    (check-pred e? (term #t))
    (check-pred e? (term (let ([x 4]) x)))
    (check-pred e? (term (let ([x (CHECK-ap f g)]) (CHECK-ap h x))))
    (check-pred e? (term (λ (x) x)))
    (check-pred e? (term (ap car (cons 1 nil))))
    (check-pred e? (term (ap (λ (x) #true) #false)))
    (check-pred e? (term #true))

    (check-pred c? (term add1))
    (check-pred c? (term 42))

    (check-pred v? (term #t))
    (check-pred v? (term #false))
    (check-pred v? (term (λ (x) x)))
    (check-pred v? (term (cons 1 nil)))

    (check-pred τ? (term (U (Num ++) ∅))) ;; numbers
    (check-pred τ? (term (U (Num ++) (Nil --) ∅))) ;; numbers
    (check-pred τ? (term (U (Num ++) (Nil ++) ∅))) ;; numbers or nil
    (check-pred τ? (term (U (Num --) (Nil --) ∅))) ;; empty
    (check-pred τ? (term (U (Num ++) (Nil --) α))) ;; numbers or (α - nil)
    (check-pred τ? (term (U (→ ++ α (U (True ++) (False ++) ∅)) ∅))) ;; functions from α to bool

    (void))
)

(define-judgment-form PureScheme
  #:mode (free-variables I O)
  #:contract (free-variables e x*)
  [
   --- Var
   (free-variables x (x))]
  [
   (free-variables e_0 (x_0 ...))
   (free-variables e_1 (x_1 ...))
   --- Cons
   (free-variables (cons e_0 e_1) (x_0 ... x_1 ...))]
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
   --- check-ap
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

(define (closed? t)
  (judgment-holds (closed ,t)))

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
     [(term #t)
      ==> #t]
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
  [(δ check-add1 integer)
   ,(+ 1 (term integer))]
  [(δ check-add1 v)
   check]
  [(δ add1 integer)
   ,(+ 1 (term integer))]
  [(δ check-car (cons v_0 v_1))
   v_0]
  [(δ check-car v)
   check]
  [(δ car (cons v_0 v_1))
   v_0]
  [(δ check-cdr (cons v_0 v_1))
   v_1]
  [(δ check-cdr v)
   check]
  [(δ cdr (cons v_0 v_1))
   v_1]
  [(δ c v)
   UNDEFINED])

(module+ test
  (test-case "δ"
    (check-equal? (term #{δ add1 5}) (term 6))
    (check-equal? (term #{δ check-add1 5}) (term 6))
    (check-equal? (term #{δ car (cons 1 nil)}) (term 1))
    (check-equal? (term #{δ check-car (cons 1 nil)}) (term 1))
    (check-equal? (term #{δ cdr (cons 1 nil)}) (term nil))
    (check-equal? (term #{δ check-cdr (cons 1 nil)}) (term nil))
    (check-equal? (term #{δ check-cdr nil}) (term check))
    (check-equal? (term #{δ cdr nil}) (term UNDEFINED))))

(define-judgment-form PureScheme
  #:mode (meaningful I)
  #:contract (meaningful e)
  [
   --- check-ap
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
      [(term (ap car nil))]
      [(term (ap 1 2))])))

;; TODO need to check 'meaningful?'
(define --->
  (reduction-relation PureScheme
   [--> (in-hole E (ap (λ (x) e) v))
        (in-hole E (substitute e x v))
        (side-condition (debug "maybe you should give up ~a" (term (ap (λ (x) e) v))))
        βv]
   [--> (in-hole E (CHECK-ap (λ (x) e) v))
        (in-hole E (substitute e x v))
        check-βv]
   [--> (in-hole E (let ([x v]) e))
        (in-hole E (substitute e x v))
        let]
   [--> (in-hole E (if v e_1 e_2))
        (in-hole E e_1)
        (side-condition (not (equal? (term v) #f)))
        if1]
   [--> (in-hole E (if #false e_1 e_2))
        (in-hole E e_2)
        if2]
   [--> (in-hole E (ap Prim v))
        (in-hole E v_1)
        (where v_1 #{δ Prim v})
        δ1]
   [--> (in-hole E (ap Prim v))
        check
        (where check #{δ Prim v})
        δ2]
   [--> (in-hole E (CHECK-ap Prim v))
        (in-hole E v_1)
        (side-condition (debug "checkap 1"))
        (where v_1 #{δ Prim v})
        check-δ1]
   [--> (in-hole E (CHECK-ap c v))
        check
        (side-condition (debug "checkap 2 ~a" (term (CHECK-ap c v))))
        (side-condition (or (not (Prim? (term c)))
                            (check? (term #{δ c v}))))
        check-δ2]
   [--> (in-hole E e)
        STUCK
        (judgment-holds (stuck e))
        stuck]))

;; Lemma 3.1: Uniform Evaluation
;;  For all closed expressions `e`, either:
;;  - `e` diverges
;;  - `e --->* check`
;;  - `e --->* v` where `v` closed
;;  - `e --->* e'` where `e'` stuck
(define --->*
  (let ([-> (reflexive-transitive-closure/deterministic --->)])
    (λ (t)
      (let ([v (-> t)])
        (if (or (check? v) (stuck? v))
          v
          (if (closed? v)
            v
            (raise-user-error '--->* "evaluating ~a gave non-closed value ~a" t v)))))))

(define-judgment-form PureScheme
  #:mode (stuck I)
  #:contract (stuck e)
  [
   (where UNDEFINED #{δ Prim v})
   --- ap
   (stuck (ap Prim v))]
  [
   (where UNDEFINED #{δ Prim v})
   --- check
   (stuck (CHECK-ap Prim v))]
  [
   --- prim
   (stuck (ap basic-constant v))])

(module+ test
  (test-case "--->"
    (check-apply* --->*
     [(term (ap (λ (x) #true) #false))
      ==> (term #true)]
     [(term (CHECK-ap (λ (x) x) #false))
      ==> (term #false)]
     [(term (ap add1 4))
      ==> (term 5)]
     [(term (cons 1 1))
      ==> (term (cons 1 1))]
     [(term (cons (ap add1 1) (CHECK-ap add1 1)))
      ==> (term (cons 2 2))]
     [(term (CHECK-ap check-add1 (λ (x) #true)))
      ==> (term check)]
     [(term (ap add1 (ap add1 0)))
      ==> (term 2)]
     [(term (ap cdr (cons 5 nil)))
      ==> (term nil)]
     [(term (let ([x (ap add1 2)]) (ap add1 x)))
      ==> (term 4)]
     [(term (CHECK-ap add1 (λ (x) #true)))
      ==> (term STUCK)]))
)

;; -----------------------------------------------------------------------------
;; 3.4 
;; types must be tidy, each tag may be used at most once within a union and type
;;  variables must have a consistent universe

;; types must have form
;; - α ∅ (U (k f τ) (¬ (k) τ) ...) (μ 
(define-judgment-form PureScheme
  #:mode (tidy I I)
  #:contract (tidy k* τ)
  [
   --- α
   (tidy k* α)]
  [
   --- ∅
   (tidy k* ∅)]
  [
   (tidy () α)
   (tidy () τ)
   --- μ
   (tidy () (μ α τ))]
  [
   (side-condition ,(not (set-member? (term k*_0) (term k))))
   (tidy () σ) ...
   (where k*_1 ,(cons (term k) (term k*_0)))
   (tidy k*_1 (U partition ∅)) ...
   --- U
   (tidy k*_0 (U (k flag σ ...) partition ... slack))])

(define-metafunction PureScheme
  [(tidy# τ)
   #true
   (judgment-holds (tidy () τ))]
  [(tidy# τ)
   #false])

(define (tidy? t)
  (term #{tidy# ,t}))

(module+ test
  (test-case "tidy"
    (check-true* tidy?
     [(term (U (Num ++) ∅))] ;; numbers
     [(term (U (Num ++) (Nil --) ∅))] ;; numbers
     [(term (U (Num ++) (Nil ++) ∅))] ;; numbers or nil
     [(term (U (Num --) (Nil --) ∅))] ;; empty
     [(term (U (Num ++) (Nil --) α))] ;; numbers or (α - nil)
     [(term (U (→ ++ α (U (True ++) (False ++) ∅)) ∅))]) ;; functions from α to bool
    (check-false* tidy?
      [(term (U (Num --) (Num ++) ∅))]))
)

;; 