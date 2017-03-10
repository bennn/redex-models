#lang mf-apply racket/base

(require
  racket/set
  (only-in racket/list
    first
    second
    rest
    cartesian-product)
  (only-in racket/random
    random-ref)
  redex/reduction-semantics
  (for-syntax racket/base syntax/parse))

(module+ test
  (require rackunit rackunit-abbrevs))

(define *debug?* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug?*)
    (printf "[DEBUG] ")
    (apply printf msg arg*)
    (newline)))

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
 [v- ::= ;; norm'd values
         (c v- ...)
         (λ x e)]
 [c ::= ;; value constructor
        cons
        A B C]
 [x* ::= (x ...)]
 ;; -----------------------------------------------------------------------------
 ;; Section 2:
 [bv* ::= (bv ...)]
 [ξ ::= ;; set environment
        ((x bv*) ...)]
 ;; -----------------------------------------------------------------------------
 ;; Section 3: Set Constraints
 [setvar ::= ;; assuming: setvar for each program variable AND setvar for each λ range
             X
             (ran (λ x e))]
 [se ::= ;; set expression
         setvar
         (λ x e)
         (c se ...)
         (apply se se)
         (case se [(c X ...) ⇒ se] [X ⇒ se])
         (ifnotempty se se)]
 [constr ::= ;; set constraint
             (se ⊆ X)]
 [conj ::= ;; conjunction of set constraints
            (constr ...)]
 [sc-value ::= ;; set constraint value, equal to v-
               (λ x e)
               (c sc-value ...)]
 [sc-value* ::= ;; set of sc-value
                (sc-value ...)]
 [IN ::= ;; interpretation (map from set-variables to set-values)
         ((setvar sc-value*) ...)]
 ;; -----------------------------------------------------------------------------
 [x X ::= ;; lowercase = program variable, uppercase = set variable
          variable-not-otherwise-mentioned]
 ;#:binding-forms
 ; (λ x e #:refers-to x)
 ; (fix x e #:refers-to x)
)
(define e? (redex-match? FL e))
(define c? (redex-match? FL c))
(define E? (redex-match? FL E))
(define bv? (redex-match? FL bv))
(define v? (redex-match? FL v))
(define v-? (redex-match? FL v-))
(define fx? (redex-match? FL fx))
(define x*? (redex-match? FL x*))
(define bv*? (redex-match? FL bv*))
(define ξ? (redex-match? FL ξ))
(define setvar? (redex-match? FL setvar))
(define se? (redex-match? FL se))
(define constr? (redex-match? FL constr))
(define conj? (redex-match? FL conj))
(define sc-value? (redex-match? FL sc-value))
(define sc-value*? (redex-match? FL sc-value*))
(define IN? (redex-match? FL IN))

(define (λ? t) (and (pair? t) (eq? 'λ (car t))))
(define (constant? t) (and (pair? t) (c? (car t))))

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

    (let ([env (term ((y (A))))])
      (check-true (e? (term (,env (λ x y)))))
      (check-false (e? env))
      (check-true (E? env)))

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
     [(term [((x (A))) (λ y x)])]
     [(term (cons (A) [((x (A))) (λ y x)]))]
     [(term (() (λ n n)))]))

  (test-case "redex-match:unorganized"
    (check-true (v-? (term (cons (A) (λ y x)))))

    (check-true (sc-value? (term (A))))
    (check-true (sc-value*? (term ((A)))))

    (check-true (setvar? (term X)))
    (check-true (setvar? (term (ran (λ x (C))))))
    (check-true (sc-value? (term (A))))
    (check-true (IN? (term ((X ((A)))))))
    (check-true (IN? (term (((ran (λ x (C))) ((C)))))))
    (check-true (IN? (term ((X ((A))) ((ran (λ x (C))) ((C)))))))
  )

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

(module+ test
  (test-case "redex-match:FL"
    (check-true (bv? (term (B))))
    (check-true (bv*? (term ((B)))))
    (check-true (ξ? (term ((x ((B)))))))))

(define-metafunction FL
  refs : ξ x -> any
  [(refs ((x_0 bv*_0) ... (x bv*) (x_1 bv*_1) ...) x)
   bv*]
  [(refs ξ x)
   ()])

(define-metafunction FL
  irefs : IN setvar -> any
  [(irefs ((setvar_0 sc-value*_0) ... (setvar sc-value*) (setvar_1 sc-value*_1) ...) setvar)
   sc-value*]
  [(irefs IN setvar)
   ()])

(define-metafunction FL
  doms : ξ -> any
  [(doms ((x bv*) ...))
   (x ...)])

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
;;      `(judgment-holds (~~> ....))` terminate when infinite proofs exist
;;; (define-metafunction FL
;;;   refs-v : ξ x -> any
;;;   [(refs-v ξ x)
;;;    v_0
;;;    (where bv* ,(filter v? (term #{refs ξ x})))
;;;    (side-condition (not (null? (term bv*))))
;;;    (where v_0 ,(random-ref (term bv*)))]
;;;   [(refs-v ξ x)
;;;    FAIL:refs-v])
;;; 
;;; (define-metafunction FL
;;;   refs-fix : ξ x -> any
;;;   [(refs-fix ξ x)
;;;    fx_0
;;;    (where bv* ,(filter fx? (term #{refs ξ x})))
;;;    (side-condition (not (null? (term bv*))))
;;;    (where fx_0 ,(random-ref (term bv*)))]
;;;   [(refs-fix ξ x)
;;;    FAIL:refs-fix])

(define-judgment-form FL
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

(define-judgment-form FL
  ;; vim seems to draw ~~> faster than ⇝
  #:mode (~~> I I O)
  #:contract (~~> ξ e v)
  [
   (where (bv_0 ... v bv_1 ...) #{refs ξ x})
   --- Var-1
   (~~> ξ x v)]
  [
   (where (bv_0 ... fx bv_1 ...) #{refs ξ x})
   (~~> ξ fx v)
   --- Var-2
   (~~> ξ x v)]
  [
   (~~> ξ e_1 (E (λ x e)))
   (~~> ξ e_2 v_2)
   (~~> ξ e v)
   --- App
   (~~> ξ (e_1 e_2) v)]
  [
   (~~> ξ e_1 v_1) ...
   --- Const
   (~~> ξ (c e_1 ...) (c v_1 ...))]
  [
   (where E ()) ;; note: not part of Figure 2, but safe
   (∈ E ξ)
   --- Abs
   (~~> ξ (λ x e) (E (λ x e)))]
  [
   (~~> ξ e_1 (c v_1 ...))
   (~~> ξ e_2 v)
   --- Case-1
   (~~> ξ (case e_1 [(c x_1 ...) ⇒ e_2] [x_3 ⇒ e_3]) v)]
  [
   (~~> ξ e_1 (c_2 v_2 ...))
   (side-condition ,(not (equal? (term c) (term c_2))))
   (~~> ξ e_3 v)
   --- Case-2
   (~~> ξ (case e_1 [(c x_1 ...) ⇒ e_2] [x_3 ⇒ e_3]) v)]
  [
   (~~> ξ e v)
   --- Fix
   (~~> ξ (fix x e) v)])

;; "Observe that this second groups of rules will, in general, lead to an
;;  unsound approximation. That is, certain set environments `ξ` will be such
;;  that for some closed terms `e0`, `⊢ e0 → v` but `ξ ¬⊢ e0 ~~> v`.
(module+ test
  (test-case "~~>:unsound"
    (let ([ξ0 (term ((x ((B)))))]
          [e0 (term ((λ x x) (A)))]
          [v (term (A))])
      (check-equal? (term (eval ,e0)) v)
      (check-false (judgment-holds (~~> ,ξ0 ,e0 (A))))))
)

(module+ test
  (test-case "~~>:simple"
    (check-true (judgment-holds
      (~~> ((x ((A) (B) (C))))
          x
          (A))))
    (check-true (judgment-holds
      (~~> ((x ((A) (B))))
          x
          (A))))
    #;(check-true (judgment-holds
      (~~> ((x ((A) (B) (fix y x))))
          x
          (A))))
    (check-true (judgment-holds
      (~~> ((x ((A) (B) (fix z (λ r r)))) (y ((A) (C))) (r ((A) (C))))
          (x y)
          (A))))
    (check-true (judgment-holds
      (~~> ((x ((A) (B))) (y ((A) (B))))
          (cons x y)
          (cons (B) (A)))))
    (check-true (judgment-holds
      (~~> ((z ((A))))
          (λ x (A))
          (() (λ x (A))))))
    (check-true (judgment-holds
      (~~> ((x ((A) (B) (C))) (y ((B) (C))) (z ((A) (B) (cons (A) (B)))))
          (case (cons (A) (B))
            [(cons x y) ⇒ x]
            [z ⇒ (C)])
          (A))))
    (check-true (judgment-holds
      (~~> ((x ((A) (B) (C))) (y ((B) (C))) (z ((A) (B) (cons (A) (B)))))
          (case (cons (A) (B))
            [(B) ⇒ (A)]
            [z ⇒ (C)])
          (C))))
    #;(check-true (judgment-holds
      (~~> ((n ((A) (B) (C)))
           (fact ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))))
          ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))
          (B))))
    (check-true (judgment-holds
      (~~> ((n ((A) (B) (C)))
           (fact ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (A)]))) (C))))
          ((fix fact (λ n (case n [(A) ⇒ (B)] [y ⇒ (fact (A))]))) (C))
          (A))))
    (check-true (judgment-holds
       (~~> ((d ((cons (A) (A)))))
            (case (cons (A) (A))
             [(A) ⇒ b]
             [d ⇒ (C)])
            (C))))
))

;; -----------------------------------------------------------------------------
;; Section 2: "ξ is safe with respect to a closed term `e0` if, for every
;;  derivation ending in `ξ ⊢ e0 ~~> v` the following four conditions are met:
;;  1. every application of the rule APP is such that `v' ∈ ξ(x)`
;;  2. every application of the rule CASE-1 is such that `vi ∈ ξ(xi)`
;;  3. every application of the rule CASE-2 is such that `c'(v1 ... vn) ∈ ξ(x)`
;;  4. every application of the rule FIX is such that `fix x e ∈ ξ(x)`

(define-judgment-form FL
  #:mode (safe I I)
  #:contract (safe ξ e)
  [
   (closed ξ e)
   (side-condition ,(let ([d* (build-derivations (~~> ξ e v))])
                      (and (not (null? d*))
                           (app-safe? (find-derivations/name d* "App"))
                           (case1-safe? (find-derivations/name d* "Case-1"))
                           (case2-safe? (find-derivations/name d* "Case-2"))
                           (fix-safe? (find-derivations/name d* "Fix")))))
   --- IsSafe
   (safe ξ e)])

(define (find-derivations/name d* n)
  (for/fold ([acc '()])
            ([d (in-list d*)])
    (append (if (string=? n (derivation-name d)) ;; if `-name` not string, we have a bigger problem
              (cons d acc)
              acc)
            (find-derivations/name (derivation-subs d) n))))

(module+ test
  (test-case "redex-match:yolo"
    (check-true (ξ? (term ((x ((B)))))))
    (check-true (e? (term (λ x x))))
    (check-true (e? (term (() (λ x x)))))))

;; TODO depends on order of sub-derivations :/
(define (app-safe? d*)
  (for/and ([d (in-list d*)])
    (define t (derivation-term d))
    (define subs (map derivation-term (derivation-subs d)))
    (debug "APP-SAFE term is ~a" t)
    (redex-let FL ([(~~> ξ (e_0 e_1) v_0) t])
      (redex-let FL ([(~~> ξ_3 e_0 (E (λ x e_3)))
                       (first subs)]
                      [(~~> ξ_6 e_1 v_1)
                       (second subs)])
        (member (term v_1) (term #{refs ξ x}))))))

(define (case1-safe? d*)
  (for/and ([d (in-list d*)])
    (define t (derivation-term d))
    (define subs (map derivation-term (derivation-subs d)))
    (debug "CASE1-SAFE term is ~a" t)
    (redex-let FL ([(~~> ξ (case e_0 [(c x_1 ...) ⇒ e_1] [x_2 ⇒ e_2]) v_0) t])
      (redex-let FL ([(~~> ξ_3 e_0 (c v_1 ...))
                       (first subs)])
        (for/and ([x (in-list (term (x_1 ...)))]
                  [v (in-list (term (v_1 ...)))])
          (member v (term #{refs ξ ,x})))))))

(define (case2-safe? d*)
  (for/and ([d (in-list d*)])
    (define t (derivation-term d))
    (define subs (map derivation-term (derivation-subs d)))
    (debug "CASE2-SAFE term is ~a" t)
    (redex-let FL ([(~~> ξ (case e_0 [(c_0 x_1 ...) ⇒ e_1] [x_2 ⇒ e_2]) v_0) t])
      (redex-let FL ([(~~> ξ_3 e_0 (c v_1 ...))
                       (first subs)])
        (and (member (term (c v_1 ...)) (term #{refs ξ x_2})) #t)))))

(define (fix-safe? d*)
  (for/and ([d (in-list d*)])
    (define t (derivation-term d))
    (define subs (map derivation-term (derivation-subs d)))
    (debug "FIX-SAFE term is ~a" t)
    (redex-let FL ([(~~> ξ (fix x e) v_0) t])
      (and (member (term (fix x e)) (term #{refs ξ x})) #t))))

(define-judgment-form FL
  #:mode (closed I I)
  #:contract (closed ξ e)
  [
   (fvs e x*)
   (where () ,(set-subtract (term x*) (term #{doms ξ})))
   ---
   (closed ξ e)])

(define-judgment-form FL
  #:mode (fvs I O)
  #:contract (fvs e (x ...))
  [
   (where x* (x))
   --- FVS-Var
   (fvs x x*)]
  [
   (fvs e x*_0) ...
   (where x* ,(if (null? (term (e ...)))
                (term ())
                (apply set-union (term (x*_0 ...)))))
   --- FVS-c
   (fvs (c e ...) x*)]
  [
   (fvs (λ x e) x*_0)
   (where x* ,(set-subtract (term x*_0) (term #{dom E})))
   --- FVS-Closure
   (fvs (E (λ x e)) x*)]
  [
   (fvs e x*_0)
   (where x* ,(set-remove (term x*_0) (term x)))
   --- FVS-Fix
   (fvs (fix x e) x*)]
  [
   (fvs e x*_0)
   (where x* ,(set-remove (term x*_0) (term x)))
   --- FVS-λ
   (fvs (λ x e) x*)]
  [
   (fvs e_0 x*_0)
   (fvs e_1 x*_1)
   (where x* ,(set-union (term x*_0) (term x*_1)))
   --- FVS-App
   (fvs (e_0 e_1) x*)]
  [
   (fvs e_0 x*_0)
   (fvs e_1 x*_1)
   (fvs e_2 x*_2)
   (where x* ,(set-union (term x*_0)
                         (set-subtract (term x*_1) (term (x_1 ...)))
                         (set-remove (term x*_2) (term x_2))))
   --- FVS-Case
   (fvs (case e_0 [(c x_1 ...) ⇒ e_1] [x_2 ⇒ e_2]) x*)])

(define-metafunction FL
  fvs# : e -> x*
  [(fvs# e)
   x*
   (judgment-holds (fvs e x*_0))
   (where x* ,(sort (term x*_0) symbol<?))])

(module+ test
  (test-case "fvs"
    (check-equal?
      (term #{fvs# x})
      (term (x)))
    (check-equal?
      (term #{fvs# (cons x1 x2)})
      (term (x1 x2)))
    (check-equal?
      (term #{fvs# (cons (A) (B))})
      (term ()))
    (check-equal?
      (term #{fvs# (A)})
      '())
    (check-equal?
      (term #{fvs# (() (λ x x))})
      '())
    (check-equal?
      (term #{fvs# (() (λ x y))})
      '(y))
    (check-equal?
      (term #{fvs# (((y (A))) (λ x y))})
      '())
    (check-equal?
      (term #{fvs# (fix z (λ n (A)))})
      '())
    (check-equal?
      (term #{fvs# (fix z (λ n (A)))})
      '())
    (check-equal?
      (term #{fvs# (fix z (λ n (z (A))))})
      '())
    (check-equal?
      (term #{fvs# (λ x x)})
      '())
    (check-equal?
      (term #{fvs# ((A) (A))})
      '())
    (check-equal?
      (term #{fvs# (x y)})
      '(x y))
    (check-equal?
      (term #{fvs# (case a [(cons b c) ⇒ d] [e ⇒ f])})
      '(a d f))
    (check-equal?
      (term #{fvs# (case a [(cons b c) ⇒ b] [e ⇒ e])})
      '(a))
    (check-equal?
      (term #{fvs# (case (A) [(cons b c) ⇒ b] [e ⇒ e])})
      '())
  )

  (test-case "closed"
    (check-false (judgment-holds (closed () x)))
    (check-false (judgment-holds (closed () (cons x1 x2))))
    (check-true (judgment-holds (closed () (cons (A) (B)))))
    (check-true (judgment-holds (closed () (A))))
    (check-true (judgment-holds (closed () (() (λ x x)))))
    (check-false (judgment-holds (closed () (() (λ x y)))))
    (check-true (judgment-holds (closed () (((y (A))) (λ x y)))))
    (check-true (judgment-holds (closed () (fix z (λ n (A))))))
    (check-true (judgment-holds (closed () (fix z (λ n (A))))))
    (check-true (judgment-holds (closed () (fix z (λ n (z (A)))))))
    (check-true (judgment-holds (closed () (λ x x))))
    (check-true (judgment-holds (closed () ((A) (A)))))
    (check-false (judgment-holds (closed () (x y))))
    (check-false (judgment-holds (closed () (case a [(cons b c) ⇒ d] [e ⇒ f]))))
    (check-false (judgment-holds (closed () (case a [(cons b c) ⇒ b] [e ⇒ e]))))
    (check-true (judgment-holds (closed () (case (A) [(cons b c) ⇒ b] [e ⇒ e]))))
    (check-false (judgment-holds (closed ()
      (case (cons (A) (A))
       [(A) ⇒ b]
       [d ⇒ (C)]))))
    (check-false (judgment-holds
      (closed ()
              (case (cons (A) (A))
               [(A) ⇒ b]
               [d ⇒ (C)]))))

    (check-true (judgment-holds
      (closed ((b ((A))))
              (case (cons (A) (A))
               [(A) ⇒ b]
               [d ⇒ (C)]))))
  )

  (test-case "pre-safe"
    (check-equal? ;; sanity check
      (length (build-derivations (~~> ((x ((A) (B) (C)))) x v)))
      3))

  (test-case "app-safe"
    (check-false (judgment-holds
      (safe () ((λ x x) (A)))))
    (check-false (judgment-holds
      (safe ((x ((B)))) ((λ x x) (A)))))
    (check-true (judgment-holds
      (safe ((x ((A)))) ((λ x x) (A)))))
    (check-true (judgment-holds
      (safe ((x ((C) (A) (B)))) ((λ x x) (A))))))

  (test-case "case1-safe"
    (check-false (judgment-holds
      (safe ((x ((A))))
            (case (cons (A) (A))
             [(cons a b) ⇒ b]
             [d ⇒ (C)]))))
    (check-true (judgment-holds
      (safe ((a ((A))) (b ((A))))
            (case (cons (A) (A))
             [(cons a b) ⇒ b]
             [d ⇒ (C)]))))
    (check-true (judgment-holds
      (safe ((a ((B) (A))) (b ((cons (B) (B)) (A))))
            (case (cons (A) (A))
             [(cons a b) ⇒ b]
             [d ⇒ (C)]))))
    (check-false (judgment-holds
      (safe ((a ((A))) (b ((B))))
            (case (cons (A) (A))
             [(cons a b) ⇒ b]
             [d ⇒ (C)]))))
  )

  (test-case "case2-safe"
    (check-false (judgment-holds
      (safe ((x ((A))))
            (case (cons (A) (A))
             [(A) ⇒ b]
             [d ⇒ (C)]))))
    (check-true (judgment-holds
      (safe ((d ((cons (A) (A)))))
            (case (cons (A) (A))
             [(A) ⇒ (B)]
             [d ⇒ (C)]))))
    (check-true (judgment-holds
      (safe ((a ((A))) (b ((A))) (d ((A) (cons (A) (A)))))
            (case (cons (A) (A))
             [(A) ⇒ b]
             [d ⇒ (C)]))))
    (check-false (judgment-holds
      (safe ((d ((A))))
            (case (cons (A) (A))
             [(A) ⇒ (B)]
             [d ⇒ (C)]))))
  )

  (test-case "fix-safe"
    (check-false (judgment-holds
      (safe () (fix x (A)))))
    (check-true (judgment-holds
      (safe ((x ((fix x (A))))) (fix x (A)))))
    (check-true (judgment-holds
      (safe ((x ((A) (B) (C) (fix x (A))))) (fix x (A)))))
    (check-true (judgment-holds
      (safe ((x ((fix x (A)))))
            (case (A) [(A) ⇒ (fix x (A))]
                      [z ⇒ (fix x (A))]))))
    (check-true (judgment-holds
      (safe ((x ((fix x (A)))) (y ((fix y (λ n (B))))))
            (case (A) [(A) ⇒ (fix y (λ n (B)))]
                      [z ⇒ (fix x (A))]))))
    (check-false (judgment-holds
      (safe ((x ((fix x (A)))) (y ((fix y (λ n (B))))))
            (case (A) [(A) ⇒ ((fix y (λ n (B))) (A))]
                      [z ⇒ (fix x (A))]))))
    (check-true (judgment-holds
      (safe ((n ((A))) (x ((fix x (A)))) (y ((fix y (λ n (B))))))
            (case (A) [(A) ⇒ ((fix y (λ n (B))) (A))]
                      [z ⇒ (fix x (A))]))))
    (check-false (judgment-holds
      (safe ((x ((fix x (A)))) (y ((B))))
            (case (A) [(A) ⇒ (fix y (λ n (B)))]
                      [z ⇒ (fix x (A))]))))
  )
)

;; -----------------------------------------------------------------------------
;; Section 2: Theorem 1: Soundness: if ξ is safe wrt a closed term e0,
;; then  `⊢ e0 → v` implies `ξ ⊢ e0 ~~> v`

(define-metafunction FL
  check-theorem-1 : ξ e -> boolean
  [(check-theorem-1 ξ e)
   #true
   (judgment-holds (safe ξ e))
   (where v (eval e))
   (judgment-holds (~~> ξ e v))]
  [(check-theorem-1 ξ e)
   ,(raise-arguments-error 'theorem-1-unsound
      "environment is safe for closed term, but does not approximate the runtime behavior"
      "set-env" (term ξ)
      "term" (term e)
      "(derived-value)" (term v))
   (judgment-holds (safe ξ e))
   (where v (eval e))]
  [(check-theorem-1 ξ e)
   #false])

(module+ test
  (test-case "theorem1:basic-pass"
    ;; check that the examples from the "safe" tests are all sound

    (check-true* (λ (x) (term #{check-theorem-1 ,(car x) ,(cadr x)}))
     [(term [((x ((A)))) ((λ x x) (A))])]
     [(term [((x ((C) (A) (B)))) ((λ x x) (A))])]
     [(term [((a ((A))) (b ((A))))
             (case (cons (A) (A))
              [(cons a b) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((a ((B) (A))) (b ((cons (B) (B)) (A))))
             (case (cons (A) (A))
              [(cons a b) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((d ((cons (A) (A)))))
             (case (cons (A) (A))
              [(A) ⇒ (B)]
              [d ⇒ (C)])])]
     [(term [((a ((A))) (b ((A))) (d ((A) (cons (A) (A)))))
             (case (cons (A) (A))
              [(A) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((x ((fix x (A))))) (fix x (A))])]
     [(term [((x ((A) (B) (C) (fix x (A))))) (fix x (A))])]
     [(term [((x ((fix x (A)))))
             (case (A) [(A) ⇒ (fix x (A))]
                       [z ⇒ (fix x (A))])])]
     [(term [((n ((A))) (x ((fix x (A)))) (y ((fix y (λ n (B))))))
             (case (A) [(A) ⇒ ((fix y (λ n (B))) (A))]
                       [z ⇒ (fix x (A))])])]))

  (test-case "theorem-1:basic-fail"
    (check-false* (λ (x) (term #{check-theorem-1 ,(car x) ,(cadr x)}))
     [(term [() ((λ x x) (A))])]
     [(term [((x ((B)))) ((λ x x) (A))])]
     [(term [((x ((A))))
             (case (cons (A) (A))
              [(cons a b) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((a ((A))) (b ((B))))
             (case (cons (A) (A))
              [(cons a b) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((x ((A))))
             (case (cons (A) (A))
              [(A) ⇒ b]
              [d ⇒ (C)])])]
     [(term [((d ((A))))
             (case (cons (A) (A))
              [(A) ⇒ (B)]
              [d ⇒ (C)])])]
     [(term [() (fix x (A))])]
     [(term [((x ((fix x (A)))) (y ((B))))
             (case (A) [(A) ⇒ (fix y (λ n (B)))]
                       [z ⇒ (fix x (A))])])]))
)

;; -----------------------------------------------------------------------------
;; Proposition 1: minimality : if ξ_1 and ξ_2 are safe wrt to a closed term
;;  `e0`, then so is `ξ_1 ∩ ξ_2`. Moreover `ξ_1 ∩ ξ_2 ⊢ e0 ~~> v` implies
;;  `ξ_1 ⊢ e_0 ~~> v` and `ξ_2 ⊢ e0 ~~> v`.

(define-metafunction FL
  check-proposition-1 : ξ ξ e -> boolean
  [(check-proposition-1 ξ_1 ξ_2 e_0)
   #true
   (judgment-holds (safe ξ_1 e_0))
   (judgment-holds (safe ξ_2 e_0))
   (where ξ_3 (∩ ξ_1 ξ_2))
   (judgment-holds (safe ξ_3 e_0))
   (judgment-holds (~~> ξ_3 e_0 v_3))
   (judgment-holds (~~> ξ_1 e_0 v_3))
   (judgment-holds (~~> ξ_2 e_0 v_3))]
  [(check-proposition-1 ξ_1 ξ_2 e_0)
   ,(raise-arguments-error 'proposition-1 "intersection of safe environment is not safe"
      "env1" (term ξ_1)
      "env2" (term ξ_2)
      "term" (term e)
      "(intersection)" (term ξ_3))
   (judgment-holds (safe ξ_1 e_0))
   (judgment-holds (safe ξ_2 e_0))
   (where ξ_3 (∩ ξ_1 ξ_2))
   (where #t ,(not (judgment-holds (safe ξ_3 e_0))))]
  [(check-proposition-1 ξ_1 ξ_2 e_0)
   ,(raise-arguments-error 'proposition-1 "intersected environment produces value not in prior approximations"
      "env1" (term ξ_1)
      "env2" (term ξ_2)
      "term" (term e_0)
      "(intersected)" (term ξ_3)
      "(derived-value)" (term v_3))
   (judgment-holds (safe ξ_1 e_0))
   (judgment-holds (safe ξ_2 e_0))
   (where ξ_3 (∩ ξ_1 ξ_2))
   (judgment-holds (safe ξ_3 e_0))
   (judgment-holds (~~> ξ_3 e_0 v_3))
   (where #f ,(and (judgment-holds (~~> ξ_1 e_0 v_3))
                   (judgment-holds (~~> ξ_2 e_0 v_3))))]
  [(check-proposition-1 ξ_1 ξ_2 e_0)
   #f
   ])

(define-metafunction FL
  ∩ : ξ ξ -> any
  [(∩ ξ_1 ())
   ξ_1]
  [(∩ () ξ_2)
   ξ_2]
  [(∩ ((x_0 bv*_0) (x_1 bv*_1) ...) ((x_2 bv*_2) ... (x_0 bv*_3) (x_4 bv*_4) ...))
   ((x_0 bv*_6) (x_5 bv*_5) ...)
   (where bv*_6 ,(set-intersect (term bv*_0) (term bv*_3)))
   (where ((x_5 bv*_5) ...) (∩ ((x_1 bv*_1) ...) ((x_2 bv*_2) ... (x_4 bv*_4) ...)))])

(module+ test
  (test-case "check-prop-1"
    (check-true* (λ (x) (term #{check-proposition-1 ,(car x) ,(cadr x) ,(caddr x)}))
     [(term [((x ((A))))
             ((x ((A) (B))))
             ((λ x x) (A))])]
     [(term [((n ((A))) (x ((fix x (A)))) (y ((fix y (λ n (B))))))
             ((n ((B) (C) (A))) (x ((fix x (A)))) (y ((fix y (λ n (B))))))
             (case (A) [(A) ⇒ ((fix y (λ n (B))) (A))]
                       [z ⇒ (fix x (A))])])]))
)

;; -----------------------------------------------------------------------------
;; Section 2: Definition 1: Set Based Approximation
;;  let `ξ_0` be the least set environment that is safe wrt `e_0`.
;;  The set based approximation of `e_0` denoted `sba(e_0)` is:
;;
;;  sba(e_0) = {v | ξ_0 ⊢ e_0 ~~> v}
;;
;; (Cannot program this because no way to pick `ξ_0`)

;; =============================================================================
;; Section 3: Main Result: Algorithm for computing `sba(e_0)`
;; - first we construct set constraints corresponding to the input term e0
;; - the second part of the algorithm is a simplification procedure for set constraints

;; The environment part of closures in `sba(e0)` is essentially redundant
;; ... define an operator ||v|| on values `v` which forgets the environment part
;; of closures
(define-judgment-form FL
  #:mode (norm I O)
  #:contract (norm v v-)
  [
   (norm v v-) ...
   --- Norm-C
   (norm (c v ...) (c v- ...))]
  [
   --- Norm-λ
   (norm (E (λ x e)) (λ x e))])

(module+ test
  (test-case "norm"
    (check-true (judgment-holds
      (norm (() (λ x (A))) (λ x (A)))))
    (check-true (judgment-holds
      (norm [((x (A)) (y (B))) (λ z ((λ a x) y))] (λ z ((λ a x) y)))))
    (check-true (judgment-holds
      (norm (cons (A) [((x (A))) (λ y x)]) (cons (A) (λ y x)))))))

;; The algorithm computes a representation of the set ||sba(e0)||

;; -----------------------------------------------------------------------------
;; 

(define-metafunction FL
  var->setvar : x -> x
  [(var->setvar x)
   ,(string->symbol (string-upcase (symbol->string (term x))))
   (side-condition (lowercase? (term x)))]
  [(var->setvar x)
   ,(raise-user-error 'var->setvar "variable ~a is a set variable (uppercase)" (term x))
   (side-condition (not (lowercase? (term x))))])

(define (lowercase? sym)
  (define str (symbol->string sym))
  (string=? str (string-downcase str)))

(module+ test
  (test-case "var->setvar"
    (check-apply* (λ (t) (term #{var->setvar ,t}))
     [(term x)
      ==> (term X)]
     [(term z)
      ==> (term Z)]
     [(term gigawatt)
      ==> (term GIGAWATT)])

    (check-exn exn:fail:user?
      (λ () (term #{var->setvar X}))))

  (test-case "lowercase?"
    (check-apply* lowercase?
     ['a
      ==> #true]
     ['A
      ==> #false]
     ['aPPle
      ==> #false]
     ['apple
      ==> #true]))
)

(define-judgment-form FL
  #:mode (interpretation I I O)
  #:contract (interpretation IN se sc-value*)
  [
   (where sc-value* #{irefs IN setvar})
   --- I-var
   (interpretation IN setvar sc-value*)]
  [
   (where (sc-value*_0 ...) (#{irefs IN se_0} ...))
   (where sc-value* ,(apply set-union
                       (map (λ (t) (list (cons (term c) t)))
                            (apply cartesian-product (term (sc-value*_0 ...))))))
   --- I-C
   (interpretation IN (c se_0 ...) sc-value*)]
  [
   --- I-λ
   (interpretation IN (λ x e) ((λ x e)))]
  [
   (interpretation IN se_0 ())
   --- I-ifnotempty-1
   (interpretation IN (ifnotempty se_0 se_1) ())]
  [
   (interpretation IN se_0 sc-value*_0)
   (side-condition ,(not (null? (term sc-value*_0))))
   (interpretation IN se_1 sc-value*)
   --- I-ifnotempty-2
   (interpretation IN (ifnotempty se_0 se_1) sc-value*)]
  [
   (interpretation IN se_0 sc-value*_0)
   (where (sc-value_0 ...) ,(filter λ? (term sc-value*_0)))
   (interpretation IN se_1 sc-value*_1)
   (side-condition ,(not (null? (term sc-value*_1))))
   ;; TODO how is this 'ran' requirement NOT just bootstrapping?
   (interpretation IN (ran sc-value_0) sc-value*_2) ...
   ;; damn
   (side-condition ,(for/and ([x (in-list (map cadr (term (sc-value_0 ...))))])
                      (subset? (term sc-value*_1) (term #{irefs IN #{var->setvar ,x}}))))
   (where sc-value* ,(apply set-union (term (sc-value*_2 ...))))
   --- I-apply
   (interpretation IN (apply se_0 se_1) sc-value*)]
  [
   (interpretation IN se_0 sc-value*_0)
   (interpretation IN se_1 sc-value*_3)
   (interpretation IN se_2 sc-value*_4)
   (where sc-value*_5 ,(filter (λ (t) (and (constant? t) (eq? (term c) (car t))))
                               (term sc-value*_0)))
   (where sc-value*_6 ,(filter (λ (t) (and (constant? t) (not (eq? (term c) (car t)))))
                               (term sc-value*_0)))
   (where sc-value*_1 ,(if (null? (term sc-value*_5)) (term ()) (term sc-value*_3)))
   (where sc-value*_2 ,(if (null? (term sc-value*_6)) (term ()) (term sc-value*_4)))
   (where sc-value* ,(set-union (term sc-value*_1) (term sc-value*_2)))
   (side-condition ,(and
                      (for/and ([cnst (in-list (term sc-value*_5))])
                        (for/and ([v (in-list (cdr cnst))]
                                  [x (in-list (term (X_1 ...)))])
                          (member v (term #{irefs IN ,x}))))
                      (let ([scv* (term #{irefs IN X_2})])
                        (for/and ([cnst (in-list (term sc-value*_6))])
                          (member cnst scv*)))))
   --- I-case
   (interpretation IN (case se_0 [(c X_1 ...) ⇒ se_1] [X_2 ⇒ se_2]) sc-value*)])

(define-metafunction FL
  interpretation# : IN se -> sc-value*
  [(interpretation# IN se)
   sc-value*
   (judgment-holds (interpretation IN se sc-value*))]
  [(interpretation# IN se)
   ,(raise-user-error 'interpretation "undefined for ~a ~a" (term IN) (term se))])

(module+ test
  (test-case "interpretation"
  (parameterize ([*debug?* #t])
    (check-apply* (λ (t) (term #{interpretation# ,(car t) ,(cadr t)}))
     [(term [((X ((A) (B) (C)))) X])
      ==> (term ((A) (B) (C)))]
     [(term [(((ran (λ x (A))) ((A))) (X ((B) (C))))
             X])
      ==> (term ((B) (C)))]
     [(term [() (A)])
      ==> (term ((A)))]
     [(term [((X ((A) (B))))
             (cons X X)])
      ==> (term ((cons (B) (B)) (cons (B) (A)) (cons (A) (B)) (cons (A) (A))))]
     [(term [() (λ x (A))])
      ==> (term ((λ x (A))))]
     [(term [() (ifnotempty X (A))])
      ==> (term ())]
     [(term [((X ((B) (C)))) (ifnotempty X (A))])
      ==> (term ((A)))]
     [(term [((X ((A)))
              ((ran (λ x (C))) ((C))))
             (apply (λ x (C)) (A))])
      ==> (term ((C)))]
     [(term [((X ((A) (λ z z)))
              (Y ((B)))
              ((ran (λ z z)) ((B)))
              (Z ((B))))
             (apply X Y)])
      ==> (term ((B)))]
     [(term [((X ((A) (λ z z)))
              (Y ((B)))
              ((ran (λ z z)) ((C) (B)))
              (Z ((C) (B))))
             (apply X Y)])
      ==> (term ((C) (B)))]
     [(term [((X ((A) (λ z z) (λ q (C))))
              (Y ((B)))
              ((ran (λ z z)) ((B)))
              ((ran (λ q (C))) ((C)))
              (Q ((B) (C) (A) (λ r r)))
              (Z ((B))))
             (apply X Y)])
      ==> (term ((C) (B)))]
     [(term [((W ((A)))
              (X ())
              (Y ())
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ Z])])
      ==> (term ((C) (B) (A)))]
     [(term [((W ((A)))
              (X ())
              (Y ())
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ W])])
      ==> (term ((A)))]
     [(term [((W ((cons (A) (A))))
              (X ((A)))
              (Y ((A)))
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ W])])
      ==> (term ((A)))]
     [(term [((W ((C) (cons (A) (A))))
              (X ((A)))
              (Y ((A)))
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ W])])
      ==> (term ((cons (A) (A)) (C) (A)))]
     [(term [((W ((cons (A) (A))))
              (X ((cons (C) (B)) (A)))
              (Y ((A)))
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ W])])
      ==> (term ((cons (C) (B)) (A)))]
     [(term [((W ((cons (A) (A))))
              (X ((A)))
              (Y ((A) (B) (C)))
              (Z ((A) (B) (C))))
             (case W [(cons X Y) ⇒ X] [Z ⇒ Z])])
      ==> (term ((A)))]
    )
  ))
)

;; An interpretation I is a model of a conjunction of constraints `C` if, for
;; each constraint `se ⊆ X` it is the case that `I(se)` is defined and
;; `I(se) ⊆ I(X)`
(define-judgment-form FL
  #:mode (⊨ I I)
  #:contract (⊨ IN C)
  [
   --- Models-Empty
   (⊨ IN ())]
  [
   (interpretation IN se sc-value*_0)
   (interpretation IN X sc-value*_1)
   (side-condition ,(and (not (null? (term sc-value*_0)))
                         (subset? (term sc-value*_0) (term sc-value*_1))))
   (⊨ IN (constr_1 ...))
   --- Models-Cons
   (⊨ IN ((se ⊆ X) constr_1 ...))])

;; -----------------------------------------------------------------------------
;; Section 3: Constructing Set Constraints


