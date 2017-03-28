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
  [unchecked-prim ::= add1 car cdr cons number? not]
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
         Num
         True
         False
         Nil
         Cons
         →]
  [flag ::= ++ -- φ]
  [Σ ::= ;; typescheme
         (∀ (ν ν ...) τ) τ]
  [S ::= ;; substitution
         (sub ...)]
  [sub ::= (φ flag) (α τ)]
  [A ::= ((x Σ) ...)]
  ;; ---
  [k* ::= ;; X in the dissertation, aka "set of k" aka "label"
          (k ...)]
  [σ* ::= (σ ...)]
  [τ* ::= (τ ...)]
  [x* ::= (x ...)]
  [ν* ::= (ν ...)]
  [α* ::= (α ...)]
  [x α φ ν ::= ;; x = program variable
             ;; α = type variable
             ;; φ = flag variable
             ;; ν = type or flag variable
             variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let ([x e_0]) e_1 #:refers-to x)
  (μ α τ #:refers-to α)
  (Σ (ν ...) τ #:refers-to (shadow ν ...)))

;; Programs are closed expressions

(define e? (redex-match? PureScheme e))
(define v? (redex-match? PureScheme v))
(define a? (redex-match? PureScheme a))
(define c? (redex-match? PureScheme c))
(define τ? (redex-match? PureScheme τ))
(define σ? τ?)
(define Σ? (redex-match? PureScheme Σ))
(define S? (redex-match? PureScheme S))
(define partition? (redex-match? PureScheme partition))
(define flag? (redex-match? PureScheme flag))
(define k? (redex-match? PureScheme k))
(define ν*? (redex-match? PureScheme ν*))
(define A? (redex-match? PureScheme A))
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
    (check-pred τ? (term (U (Num ++) (True --) (Cons ++ ∅ ∅) α)))
    (check-pred τ? (term (μ α (U (Nil ++) (Cons ++ τ α) ∅))))
    (check-pred τ? (term (U (→ ++ (U (Num ++) ∅) (U (Num ++) ∅)) ∅)))
    (check-pred τ? (term (U (→ b a a) ∅)))

    (check-pred ν*? (term (a b)))

    (check-pred S? (term ((a (U (Num ++) ∅)) (b ++))))

    (check-pred Σ? (term (∀ (a b) (U (→ b α α) ∅))))

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
  [(δ number? integer)
   #true]
  [(δ number? v)
   #false]
  [(δ not #false)
   #true]
  [(δ not v)
   #false]
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
    (check-equal? (term #{δ cdr nil}) (term UNDEFINED))
    (check-equal? (term #{δ number? nil}) (term #false))
    (check-equal? (term #{δ not #false}) (term #true))))

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
     [(term (ap number? 4))
      ==> (term #true)]
     [(term (ap not 2))
      ==> (term #false)]
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

;; "Types represent regular trees with the tags `k` constructing internal nodes.
;;  In a constructed type `(U (k f σ1 ... σn) τ)` the constructor `k` has `n+2` args:
;;  - `σ1 ... σn`
;;  - `f`
;;  - `τ`"
;; Thats a little weird for me, that `τ` is an argument to `k`.
;; As long as `tidy` is correct we're fine.

;; The range of a type variable that appears in a union type excludes types
;; built from the tags of partitions preceding it.

(define-metafunction PureScheme
  tags : τ -> k*
  [(tags slack)
   ()]
  [(tags (μ α τ))
   #{tags τ}]
  [(tags (U partition ... slack))
   ,(map car (term (partition ...)))])

(module+ test
  (test-case "tags"
    (check-equal?
      (term #{tags (U (Num ++) (True --) (Cons ++ ∅ ∅) α)})
      (term (Num True Cons))))
)

;; Types assigned to program identifiers have label ()
;; Recursive types represent infinite regular trees
;; Recursive types must be formally contractive
(define-judgment-form PureScheme
  #:mode (contractive I)
  #:contract (contractive any)
  [
   --- slack
   (contractive slack)]
  [
   (contractive partition) ...
   --- union
   (contractive (U partition ... slack))]
  [
   (contractive σ) ...
   --- partition
   (contractive (k flag σ ...))]
  [
   (side-condition ,(not (equal? (term α) (term τ))))
   (strictly-positive α τ)
   --- rec
   (contractive (μ α τ))])

(define-judgment-form PureScheme
  #:mode (strictly-positive I I)
  #:contract (strictly-positive α τ)
  [
   --- slack
   (strictly-positive α slack)]
  [
   --- union
   (strictly-positive α (U partition ... slack))]
  [
   (strictly-negative α τ_1)
   (strictly-positive α τ_2)
   --- arrow
   (strictly-positive α (→ flag τ_1 τ_2))]
  [
   (side-condition ,(not (equal? (term →) (term k))))
   (strictly-positive α τ) ...
   --- k
   (strictly-positive α (k flag τ ...))]
  [
   (strictly-positive α τ)
   --- rec
   (strictly-positive α (μ α_1 τ))])

(define-judgment-form PureScheme
  #:mode (strictly-negative I I)
  #:contract (strictly-negative α τ)
  [
   (side-condition ,(not (equal? (term α) (term slack))))
   --- slack
   (strictly-negative α slack)]
  [
   --- union
   (strictly-negative α (U partition ... slack))]
  [
   (strictly-positive α τ_1)
   (strictly-negative α τ_2)
   --- arrow
   (strictly-negative α (→ flag τ_1 τ_2))]
  [
   (side-condition ,(not (equal? (term →) (term k))))
   (strictly-negative α τ) ...
   --- k
   (strictly-negative α (k flag τ ...))]
  [
   (strictly-negative α τ)
   --- rec
   (strictly-negative α (μ α_1 τ))])

(module+ test
  (test-case "contractive"
    (check-true* values
     [(judgment-holds (contractive (U (Num ++) ∅)))]
     [(judgment-holds (contractive (μ α (U (→ Int α) ∅))))]
     [(judgment-holds (contractive (μ α (U (Nil ++) (Cons ++ τ α) ∅))))])
    (check-false* values
     [(judgment-holds (contractive (μ α α)))]
     ;; TODO ?
     #;[(judgment-holds (contractive (μ α (U (→ α Int) ∅))))])
  )
)

(define-metafunction PureScheme
  neg-flag? : partition -> boolean
  [(neg-flag? (k -- σ ...))
   #true]
  [(neg-flag? partition)
   #false])

(define-metafunction PureScheme
  normalize : τ -> τ
  [(normalize slack)
   slack]
  [(normalize (μ α τ))
   (μ α #{normalize τ})]
  [(normalize (U partition ... slack))
   slack
   (where (#t ...) (#{neg-flag? partition} ...))]
  [(normalize (U partition ... slack))
   (U ,@(sort (term (partition ...)) symbol<? #:key car) slack)])

(define-judgment-form PureScheme
  #:mode (τ=? I I)
  #:contract (τ=? τ τ)
  [
   (where τ_2 #{normalize τ_0})
   (where τ_2 #{normalize τ_1})
   ---
   (τ=? τ_0 τ_1)])

(module+ test
  (test-case "τ=?"
    (check-true* values
     [(judgment-holds (τ=? (U (Nil --) ∅) ∅))]
     [(judgment-holds (τ=? (U (True ++) (False ++) ∅) (U (False ++) (True ++) ∅)))])
  )
)

(define-metafunction PureScheme
  substitute* : S τ -> τ
  [(substitute* () τ)
   τ]
  [(substitute* ((α σ) sub ...) τ)
   (substitute* (sub ...) (subst/flat τ α σ))]
  [(substitute* ((φ flag) sub ...) τ)
   (substitute* (sub ...) (substitute τ φ flag))])

(define-metafunction PureScheme
  subst/flat : τ α σ -> τ
  [(subst/flat α α σ)
   σ]
  [(subst/flat slack α σ)
   slack]
  [(subst/flat (μ α τ) α σ)
   (μ α τ)]
  [(subst/flat (μ α_0 τ) α_1 σ)
   (μ α_0 #{subst/flat τ α_1 σ})]
  [(subst/flat (U partition_0 ... α) α σ)
   (U partition_2 ... partition_1 ... slack)
   (where (partition_2 ...) ,(for/list ([p (in-list (term (partition_0 ...)))])
                               (list* (car p)
                                      (cadr p)
                                      (for/list ([τ (in-list (cddr p))])
                                        (term #{subst/flat ,τ α σ})))))
   (where (U partition_1 ... slack) σ)]
  [(subst/flat (U partition_0 ... α) α σ)
   (U partition_2 ... slack_1)
   (where (partition_2 ...) ,(for/list ([p (in-list (term (partition_0 ...)))])
                               (list* (car p)
                                      (cadr p)
                                      (for/list ([τ (in-list (cddr p))])
                                        (term #{subst/flat ,τ α σ})))))
   (where slack_1 σ)]
  [(subst/flat (U partition_0 ... slack) α σ)
   (U partition_2 ... slack)
   (where (partition_2 ...) ,(for/list ([p (in-list (term (partition_0 ...)))])
                               (list* (car p)
                                      (cadr p)
                                      (for/list ([τ (in-list (cddr p))])
                                        (term #{subst/flat ,τ α σ})))))])

(define-metafunction PureScheme
  dom : any -> x*
  [(dom ())
   ()]
  [(dom any)
   ,(sort (map car (term any)) symbol<?)
   (side-condition (pair? (term any)))
   (side-condition (andmap pair? (term any)))])

;; special "<", looks like "subtype"
(define-judgment-form PureScheme
  #:mode (instance I I I)
  #:contract (instance S τ Σ)
  [
   (where ν* #{dom S})
   (where τ_0 #{substitute* S τ_1})
   ---
   (instance S τ_0 (∀ ν* τ_1))])

(module+ test
  (test-case "instance"
    (check-true* values
     [(judgment-holds (instance ((a (U (Num ++) ∅)) (b ++))
                                (U (→ ++ (U (Num ++) ∅) (U (Num ++) ∅)) ∅)
                                (∀ (a b) (U (→ b a a) ∅))))])
    (let ([ts (term (∀ (f1 f2) (U (Num f1) (Nil f2) ∅)))])
      (check-true* values
       [(judgment-holds (instance ((f1 ++) (f2 ++)) (U (Num ++) (Nil ++) ∅) ,ts))]
       [(judgment-holds (instance ((f1 --) (f2 ++)) (U (Num --) (Nil ++) ∅) ,ts))]
       [(judgment-holds (instance ((f1 --) (f2 --)) (U (Num --) (Nil --) ∅) ,ts))]
       [(judgment-holds (instance ((f1 ++) (f2 --)) (U (Num ++) (Nil --) ∅) ,ts))]))

    (let ([num (term (∀ (a) (U (Num ++) a)))])
      (check-true* values
       [(judgment-holds (instance ((a ∅)) (U (Num ++) ∅) ,num))]
       [(judgment-holds (instance ((a (U (True ++) ∅))) (U (Num ++) (True ++) ∅) ,num))]
       [(judgment-holds (instance ((a (U (False ++) ∅))) (U (Num ++) (False ++) ∅) ,num))]
       [(judgment-holds (instance ((a (U (True ++) (False ++) ∅))) (U (Num ++) (True ++) (False ++) ∅) ,num))]))
  )
)

;; checked primitives accept all inputs
(define-metafunction PureScheme
  typeof : c -> Σ
  [(typeof check-add1)
   (∀ (α1 α2 α3 φ1) (U (→ ++ (U (Num φ1) α3) (U (Num ++) α1)) α2))]
  [(typeof check-car)
   (∀ (α1 α2 α3 α4 φ1) (U (→ ++ (U (Cons φ1 α1 α2) α4) α1) α3))]
  [(typeof check-cdr)
   (∀ (α1 α2 α3 α4 φ1) (U (→ ++ (U (Cons φ1 α1 α2) α4) α2) α3))]
  [(typeof add1)
   ;; bad version (causes reverse-flow, does not have ∅ as subtype of input type)
   ;; (∀ (α1 α2) (U (→ ++ (U (Num ++) ∅) (U (Num ++) α1)) α2))
   (∀ (α1 α2 φ) (U (→ ++ (U (Num φ) ∅) (U (Num ++) α1)) α2))]
  [(typeof integer)
   (∀ (α) (U (Num ++) α))]
  [(typeof #true)
   (∀ (α) (U (True ++) α))]
  [(typeof #false)
   (∀ (α) (U (False ++) α))]
  [(typeof number?)
   (∀ (α1 α2 α3) (U (→ ++ α1 (U (True ++) (False ++) α2)) α3))]
  [(typeof not)
   (∀ (α1 α2 α3) (U (→ ++ α1 (U (True ++) (False ++) α2)) α3))]
  [(typeof cons)
   (∀ (α1 α2 α3 α4) (U (→ ++ α1 (U (→ ++ α2 (U (Cons ++ α1 α2) ∅)) α3)) α4))]
  [(typeof car)
   (∀ (α1 α2 α3 φ) (U (→ ++ (U (Cons φ α1 α2) ∅) α1) α3))]
  [(typeof cdr)
   (∀ (α1 α2 α3 φ) (U (→ ++ (U (Cons φ α1 α2) ∅) α2) α3))])

(module+ test
  (check-true* Σ?
   [(term #{typeof check-add1})]
   [(term #{typeof check-car})]
   [(term #{typeof check-cdr})]
   [(term #{typeof add1})]
   [(term #{typeof 4})]
   [(term #{typeof #true})]
   [(term #{typeof #false})]
   [(term #{typeof number?})]
   [(term #{typeof not})]
   [(term #{typeof cons})]
   [(term #{typeof car})]
   [(term #{typeof cdr})]))

;; -----------------------------------------------------------------------------
;; Section 3.5 static type checking

;; A judgment `A ⊢ e : τ` is a typing.
;; A term `e` is untypeable if there is no type `τ'` such that `A ⊢ e : τ'` holds

(define-metafunction PureScheme
  A-add : A [x ↦ Σ] -> A
  [(A-add A [x ↦ Σ])
   ((x_0 Σ_0) ... (x Σ) (x_2 Σ_2) ...)
   (where ((x_0 Σ_0) ... (x Σ_1) (x_2 Σ_2) ...) A)]
  [(A-add A [x ↦ Σ])
   ,(cons (term (x Σ)) (term A))])

(define-metafunction PureScheme
  A-ref : A x -> Σ
  [(A-ref A x)
   Σ
   (where ((x_0 Σ_0) ... (x Σ) (x_1 Σ_1) ...) A)])

(define-metafunction PureScheme
  A-cod : A -> Σ*
  [(A-cod A)
   (Σ ...)
   (where ((α Σ) ...) A)])

(define-metafunction PureScheme
  infer-substitution# : τ Σ -> S
  [(infer-substitution# τ_0 τ_1)
   ()]
  [(infer-substitution# τ_0 (∀ (ν ...) τ_1))
   ((ν ∅) ...)])

(define-judgment-form PureScheme
  #:mode (⊢ I I I O)
  #:contract (⊢ A e τ* τ*)
  [
   (where Σ #{typeof c})
   (where S #{infer-substitution# τ_0 Σ})
   (instance S τ_0 Σ)
   --- const⊢
   (⊢ A c (τ_0 τ_1 ...) (τ_1 ...))]
  [
   (instance () τ_0 #{A-ref x})
   --- id⊢
   (⊢ A x (τ_0 τ_1 ...) (τ_1 ...))]
  [
   (⊢ A e_1 ((U (→ ++ τ_2 τ_1) ∅) τ_3 ...) (τ_4 ...))
   (⊢ A e_2 (τ_2 τ_4 ...) (τ_5 ...))
   --- ap⊢
   (⊢ A (ap e_1 e_2) (τ_1 τ_2 τ_3 ...) (τ_5 ...))]
  [
   (⊢ A e_1 ((U (→ ++ τ_2 τ_1) τ_3) τ_4 ...) (τ_5 ...))
   (⊢ A e_2 (τ_2 τ_5 ...) (τ_6 ...))
   --- CHECK-ap⊢
   (⊢ A (CHECK-ap e_1 e_2) (τ_1 τ_2 τ_3 τ_4 ...) (τ_6 ...))]
  [
   (⊢ #{A-add A [x ↦ τ_1]} e (τ_2 τ_4 ...) (τ_5 ...))
   --- lam⊢
   (⊢ A (λ (x) e) ((U (→ ++ τ_1 τ_2) τ_3) τ_4 ...) (τ_5 ...))]
  [
   (⊢ A e_1 (τ_1 τ_3 ...) (τ_4 ...))
   (⊢ A e_2 (τ_2 τ_4 ...) (τ_5 ...))
   (⊢ A e_3 (τ_2 τ_5 ...) (τ_6 ...))
   --- if⊢
   (⊢ A (if e_1 e_2 e_3) (τ_2 τ_1 τ_3 ...) (τ_6 ...))]
  [
   (⊢ A e_1 (τ_1 τ_3 ...) (τ_4 ...))
   (⊢ #{A-add A [x ↦ #{Close τ_1 A}]} e_2 (τ_2 τ_4 ...) (τ_5 ...))
   --- let⊢
   (⊢ A (let ([x e_1]) e_2) (τ_2 τ_1 τ_3 ...) (τ_5 ...))]
)

(define-judgment-form PureScheme
  #:mode (FV I O)
  [
   (FV τ α*_1)
   (where α*_2 ,(set-subtract (term α*_1) (term α*_0)))
   --- Σ
   (FV (∀ α*_0 τ) α*_2)]
  [
   (FV τ ν*_0)
   (where ν*_1 ,(set-remove (term ν*_0) (term α)))
   --- μ
   (FV (μ α τ) ν*_1)]
  [
   --- α
   (FV α (α))]
  [
   --- ∅
   (FV ∅ ())]
  [
   (FV partition ν*_0) ...
   (FV slack ν*_1)
   (where ν*_2 ,(set-union* (cons (term ν*_1) (term (ν*_0 ...)))))
   --- U
   (FV (U partition ... slack) ν*_2)]
  [
   (FV σ ν*_1) ...
   (where ν*_2 ,(set-union* (term (ν*_1 ...))))
   --- partition
   (FV (k flag σ ...) ν*_2)])

(module+ test
  (test-case "FV"
  )
)

(define-metafunction PureScheme
  FV# : any -> any
  [(FV# Σ)
   α*
   (judgment-holds (FV Σ α*))]
  [(FV# τ)
   α*
   (judgment-holds (FV τ α*))]
  [(FV# A)
   ,(set-union* (term (α* ...)))
   (where (Σ ...) #{A-cod A})
   (where (α* ...) (#{FV# Σ} ...))]
  [(FV# Σ)
   ,(raise-user-error 'FV "undefined for ~a" (term Σ))])

(define (set-union* set*)
  (if (null? set*)
    '()
    (for/fold ([acc (car set*)])
              ([st (in-list set*)])
      (set-union acc st))))

(module+ test
  (test-case "FV"
    (check-apply* (λ (t) (term #{FV# ,t}))
     [(term (U (Num ++) ∅))
      ==> (term ())]
     [(term (∀ (a1) (U (Num ++) ∅)))
      ==> (term ())]
     [(term (U (→ ++ α β) ∅))
      ==> (term (α β))]
     [(term (∀ (α) (U (→ ++ α β) ∅)))
      ==> (term (β))])))

;; Return a typescheme that quatifies over free vars in τ
;;  but NOT freevars in A
(define-metafunction PureScheme
  Close : τ A -> Σ
  [(Close τ A)
   (∀ ν*_2 τ)
   (where ν*_0 #{FV# τ})
   (where ν*_1 #{FV# A})
   (where ν*_2 ,(set-subtract (term ν*_0) (term ν*_1)))])

(define-metafunction PureScheme
  well-typed : e τ* -> boolean
  [(well-typed e τ*)
   #true
   (judgment-holds (⊢ () e τ* ()))]
  [(well-typed e τ*)
   ,(raise-user-error 'well-typed "extra types ~a" (term τ*_1))
   (judgment-holds (⊢ () e τ* τ*_1))]
  [(well-typed e τ)
   #false])

;; Theorem: type soundness,
;; - if `⊢ e : τ` then `e` diverges or `e -->* v` and `⊢ v : τ`

;; Theorem: if program in "Stuck" there's no τ that can type it.

(module+ test
  (test-case "well-typed"
  (parameterize ([*debug* #t])
    (check-true* values
     [(term #{well-typed 4 ((U (Num ++) ∅))})]
    )
    )
  )
)

