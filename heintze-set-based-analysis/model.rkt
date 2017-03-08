#lang mf-apply racket/base

(require
  racket/set
  (only-in racket/random
    random-ref)
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

;; =============================================================================

;; Section 2: "Consider a simple call-by-value functional language"
(define-language FL
 [e ::= ;; expressions
        x
        v
        fx
        (c e ...)
        (λ x e)
        (e e)
        (case e [(c e ...) ⇒ e] [x ⇒ e])]
 [fx ::= ;; fixpoint
         (fix x e)]
 [E ::= ;; environments
        ((x bv) ...)]
 [bv ::= ;; binding value
         v
         fx]
 [v ::= ;; values
        (c v ...)
        (E (λ x e))]
 [c ::= ;; value constructor
        cons
        A B C]
 [x ::= variable-not-otherwise-mentioned]
 ;#:binding-forms
 ; (λ x e #:refers-to x)
 ; (fix x e #:refers-to x)
)
(define e? (redex-match? FL e))
(define E? (redex-match? FL E))
(define bv? (redex-match? FL bv))
(define v? (redex-match? FL v))
(define fx? (redex-match? FL fx))

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
   (where fx #{ref E x})
   (→ E fx v)
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
;; Section 2: "We now modify the operational semantics so that dependencies
;;  between variables are ignored"

(define-extended-language FLS FL
 [bv* ::= (bv ...)]
 [ξ ::= ;; set environment
        ((x bv*) ...)])
(define bv*? (redex-match? FLS bv*))
(define ξ? (redex-match? FLS ξ))

(module+ test
  (test-case "redex-match:FLS"
    (check-true (bv? (term (B))))
    (check-true (bv*? (term ((B)))))
    (check-true (ξ? (term ((x ((B)))))))))

(define-metafunction FLS
  refs : ξ x -> bv*
  [(refs ((x_0 bv*_0) ... (x bv*) (x_1 bv*_1) ...) x)
   bv*])

(module+ test
  (test-case "refs"
    (let ([ξ (term ((x ((A) (B))) (y ((B) (fix z (A)) (C)))))])
      (check-equal?
        (term (refs ,ξ x))
        (term ((A) (B))))
      (check-equal?
        (term (refs ,ξ y))
        (term ((B) (fix z (A)) (C)))))))

;;; --- these 'refs' functions were an attempt to make
;;      `(judgment-holds (~> ....))` terminate when infinite proofs exist
;;; (define-metafunction FLS
;;;   refs-v : ξ x -> any
;;;   [(refs-v ξ x)
;;;    v_0
;;;    (where bv* ,(filter v? (term #{refs ξ x})))
;;;    (side-condition (not (null? (term bv*))))
;;;    (where v_0 ,(random-ref (term bv*)))]
;;;   [(refs-v ξ x)
;;;    FAIL:refs-v])
;;; 
;;; (define-metafunction FLS
;;;   refs-fix : ξ x -> any
;;;   [(refs-fix ξ x)
;;;    fx_0
;;;    (where bv* ,(filter fx? (term #{refs ξ x})))
;;;    (side-condition (not (null? (term bv*))))
;;;    (where fx_0 ,(random-ref (term bv*)))]
;;;   [(refs-fix ξ x)
;;;    FAIL:refs-fix])

(define-judgment-form FLS
  #:mode (∈ I I)
  #:contract (∈ E ξ)
  [
   --- In-Empty
   (∈ () ξ)]
  [
   (where ((x_2 bv*_2) ... (x_0 (bv_3 ... bv_0 bv_4 ...)) (x_3 bv*_5) ...) ξ)
   (∈ ((x_1 bv_1) ...) ξ)
   --- In-Var
   (∈ ((x_0 bv_0) (x_1 bv_1) ...) ξ)])

(module+ test
  (test-case "∈"
    (check-true (judgment-holds (∈ () ())))
    (check-true (judgment-holds (∈ ((x (A))) ((x ((A)))))))
    (check-true (judgment-holds (∈ ((x (A))) ((x ((A) (B) (C)))))))
    (check-true (judgment-holds (∈ ((x (A)) (y (A))) ((y ((B) (A))) (x ((A) (B) (C)))))))

    (check-false (judgment-holds (∈ ((x (A))) ())))))

(define-judgment-form FLS
  ;; vim seems to draw ~> faster than ⇝
  #:mode (~> I I O)
  #:contract (~> ξ e v)
  [
   (where (bv_0 ... v bv_1 ...) #{refs ξ x})
   --- Var-1
   (~> ξ x v)]
  [
   (where (bv_0 ... fx bv_1 ...) #{refs ξ x})
   (~> ξ fx v)
   --- Var-2
   (~> ξ x v)]
  [
   (~> ξ e_1 (E (λ x e)))
   (~> ξ e_2 v_2)
   (~> ξ e v)
   --- App
   (~> ξ (e_1 e_2) v)]
  [
   (~> ξ e_1 v_1) ...
   --- Const
   (~> ξ (c e_1 ...) (c v_1 ...))]
  [
   (where E ()) ;; note: not part of Figure 2, but safe
   (∈ E ξ)
   --- Abs
   (~> ξ (λ x e) (E (λ x e)))]
  [
   (~> ξ e_1 (c v_1 ...))
   (~> ξ e_2 v)
   --- Case-1
   (~> ξ (case e_1 [(c x_1 ...) ⇒ e_2] [x_3 ⇒ e_3]) v)]
  [
   (~> ξ e_1 (c_2 v_2 ...))
   (side-condition ,(not (equal? (term c) (term c_2))))
   (~> ξ e_3 v)
   --- Case-2
   (~> ξ (case e_1 [(c x_1 ...) ⇒ e_2] [x_3 ⇒ e_3]) v)]
  [
   (~> ξ e v)
   --- Fix
   (~> ξ (fix x e) v)])

;; "Observe that this second groups of rules will, in general, lead to an
;;  unsound approximation. That is, certain set environments `ξ` will be such
;;  that for some closed terms `e0`, `⊢ e0 → v` but `ξ ¬⊢ e0 ~> v`.
(module+ test
  (test-case "~>:unsound"
    (let ([ξ0 (term ((x ((B)))))]
          [e0 (term ((λ x x) (A)))]
          [v (term (A))])
      (check-equal? (term (eval ,e0)) v)
      (check-false (judgment-holds (~> ,ξ0 ,e0 (A))))))
)

(module+ test
  (test-case "~>:simple"
    (check-true (judgment-holds
      (~> ((x ((A) (B) (C))))
          x
          (A))))
    (check-true (judgment-holds
      (~> ((x ((A) (B))))
          x
          (A))))
    #;(check-true (judgment-holds
      (~> ((x ((A) (B) (fix y x))))
          x
          (A))))
    (check-true (judgment-holds
      (~> ((x ((A) (B) (fix z (λ r r)))) (y ((A) (C))) (r ((A) (C))))
          (x y)
          (A))))
    (check-true (judgment-holds
      (~> ((x ((A) (B))) (y ((A) (B))))
          (cons x y)
          (cons (B) (A)))))
    (check-true (judgment-holds
      (~> ((z ((A))))
          (λ x (A))
          (() (λ x (A))))))
    (check-true (judgment-holds
      (~> ((x ((A) (B) (C))) (y ((B) (C))) (z ((A) (B) (cons (A) (B)))))
          (case (cons (A) (B))
            [(cons x y) ⇒ x]
            [z ⇒ (C)])
          (A))))
    (check-true (judgment-holds
      (~> ((x ((A) (B) (C))) (y ((B) (C))) (z ((A) (B) (cons (A) (B)))))
          (case (cons (A) (B))
            [(B) ⇒ (A)]
            [z ⇒ (C)])
          (C))))
    #;(check-true (judgment-holds
      (~> ((n ((A) (B) (C)))
           (fact ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))))
          ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))
          (B))))
    (check-true (judgment-holds
      (~> ((n ((A) (B) (C)))
           (fact ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (A)]))) (C))))
          ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))
          (A))))
))

;; -----------------------------------------------------------------------------

