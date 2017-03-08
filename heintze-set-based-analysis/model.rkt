#lang mf-apply racket/base

(require
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

;; =============================================================================

;; Section 2: "Consider a simple call-by-value functional language"
(define-language FL
 [e ::= ;; expressions
        x
        v
        (c e ...)
        (λ x e)
        (e e)
        (case e [(c e ...) ⇒ e] [x ⇒ e])
        (fix x e)]
 [E ::= ;; environments
        ((x bv) ...)]
 [bv ::= ;; binding value
         v
         (fix x e)]
 [v ::= ;; values
        (c v ...)
        (E (λ x e))]
 [c ::= ;; value constructor
        cons
        A B C]
 [x ::= variable-not-otherwise-mentioned])

(define-metafunction FL
  dom : E -> (x ...)
  [(dom ((x bv) ... ))
   (x ...)])

(define-metafunction FL
  ref : E x -> bv
  [(ref ((x_0 bv_0) ... (x bv) (x_1 bv_1) ...) x)
   bv])

(define-metafunction FL
  update : E [x ↦ bv] ... -> E
  [(update E [x ↦ bv] ...)
   ((x bv) ... (x_1 bv_1) ...)
   (where ((x_1 bv_1) ...) #{remove* E x ...})])

(define-metafunction FL
  remove* : E x ... -> E
  [(remove* E)
   E]
  [(remove* E x_0 x_1 ...)
   (remove* (remove E x_0) x_1 ...)])

(define-metafunction FL
  remove : E x -> E
  [(remove E x)
   ((x_1 bv_1) ... (x_2 bv_2) ...)
   (where ((x_1 bv_1) ... (x bv) (x_2 bv_2) ...) E)]
  [(remove E x)
   E])

(define-metafunction FL
  eval : e -> v
  [(eval e)
   v
   (judgment-holds (→ () e v))]
  [(eval e)
   ,(raise-user-error 'FL:eval "undefined for term ~a" (term e))])

;; Figure 1
(define-judgment-form FL
  #:mode (→ I I O)
  #:contract (→ E e v)
  [
   (where v #{ref E x})
   --- Var-1
   (→ E x v)]
  [
   (where (fix x e) #{ref E x})
   (→ E (fix x e) v)
   --- Var-2
   (→ E x v)]
  [
   (→ E e_1 (E_3 (λ x e)))
   (→ E e_2 v_2)
   (where E_4 #{update E_3 [x ↦ v_2]})
   (→ E_4 e v)
   --- App
   (→ E (e_1 e_2) v)]
  [
   (→ E e v) ...
   --- Const
   (→ E (c e ...) (c v ...))]
  [
   --- Abs
   (→ E (λ x e) (E (λ x e)))]
  [
   (→ E e_1 (c_1 v_1 ...))
   (where E_1 #{update E [x_1 ↦ v_1] ...})
   (→ E_1 e_2 v)
   --- Case-1
   (→ E (case e_1 [(c_1 x_1 ...) ⇒ e_2] [x_2 ⇒ e_3]) v)]
  [
   (→ E e_1 (c_2 v_2 ...))
   (side-condition ,(not (equal? (term c_1) (term c_2))))
   (where E_1 #{update E [x_2 ↦ (c_2 v_2 ...)]})
   (→ E_1 e_3 v)
   --- Case-2
   (→ E (case e_1 [(c_1 x_1 ...) ⇒ e_2] [x_2 ⇒ e_3]) v)]
  [
   (where E_1 #{update E [x ↦ (fix x e)]})
   (→ E_1 e v)
   --- Fix
   (→ E (fix x e) v)])

(module+ test
  (define e? (redex-match? FL e))
  (define E? (redex-match? FL E))
  (define bv? (redex-match? FL bv))
  (define v? (redex-match? FL v))

  (test-case "FL:redex-match"
    (check-true* e?
     [(term x)]
     [(term y)]
     [(term (A))]
     [(term (cons (A) (A)))]
     [(term (λ x (B)))]
     [(term (x y))]
     [(term (case (cons (C) (B)) [(cons x y) ⇒ x] [y ⇒ (A)]))]
     [(term (fix z (λ n (z n))))]
     [(term (cons (A) (B)))]
     [(term (case (cons (A) (B))
             [(cons x y) ⇒ x]
             [z ⇒ (C)]))])

    (check-true* E?
     [(term ())]
     [(term ((x1 (A)) (x2 (B))))]
     [(term ((x (() (λ n n))) (y (fix z (λ n (C))))))])

    (check-true* bv?
     [(term (A))]
     [(term (cons (A) (A)))]
     [(term (fix n (λ z (B))))])

    (check-true* v?
     [(term (B))]
     [(term (cons (A) (B)))]
     [(term (() (λ n n)))]))

  (test-case "dom"
    (check-apply* (λ (x) (term (dom ,x)))
     [(term ())
      ==> (term ())]
     [(term ((a (A)) (b (B)) (c (A))))
      ==> (term (a b c))]))

  (test-case "update"
    (check-equal?
      (term (ref (update () [x ↦ (A)]) x))
      (term (A)))
    (check-equal?
      (term (ref (update ((x (B))) [x ↦ (A)]) x))
      (term (A)))
    (let ([E (term (update () [x ↦ (A)] [y ↦ (B)]))])
      (check-equal? (term (ref ,E x)) (term (A)))
      (check-equal? (term (ref ,E y)) (term (B)))))

  (test-case "remove"
    (check-equal?
      (term (ref (remove ((x (A)) (y (B))) x) y))
      (term (B))))

  (test-case "eval"
    (check-apply* (λ (t) (term (eval ,t)))
     [(term (A))
      ==> (term (A))]
     [(term (cons (A) (B)))
      ==> (term (cons (A) (B)))]
     [(term ((λ x x) (A)))
      ==> (term (A))]
     [(term ((λ x (x (A))) (fix y (λ z z))))
      ==> (term (A))]
     [(term (case (cons (A) (B))
             [(cons x y) ⇒ x]
             [z ⇒ (C)]))
      ==> (term (A))]
     [(term (case (cons (A) (B))
             [(A) ⇒ x]
             [z ⇒ z]))
      ==> (term (cons (A) (B)))]))
)

;; -----------------------------------------------------------------------------
;; Section 2: "We now modifu the operational semantics so that dependencies
;;  between variables are ignored"
