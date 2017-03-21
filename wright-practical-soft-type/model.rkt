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

(define-language Λ
  [e ::= v (e e) (one e e) (let ([x e]) e)]
  [v ::= c x (λ (x) e) (one v v)]
  [c ::= ;; Const
         basic-constants
         primitive-operations]
  [a ::= ;; answers
         v CHECK]
  [E ::= ;; evaluation context
         hole (E e) (v E) (one E e) (one v E) (let ([x E]) e)]
  [basic-constants ::= integer TRUE FALSE none one]
  [primitive-operations ::= + - * / add1 not first rest]
  ;; --- Section 2.3
  [τ ::= τ-base (→ τ τ) (listof τ) α]
  [τ-base ::= bool num listof-num]
  [Σ ::= ;; type scheme
         (∀ α* τ) τ]
  [A ::= ((x Σ) ...)]
  [S ::= ;; substitution
         ((α τ) ...)]
  ;; 
  [α* ::= (α ...)]
  [x* ::= (x ...)]
  [τ* ::= (τ ...)]
  [Σ* ::= (Σ ...)]
  [x α ::= variable-not-otherwise-mentioned]
  #:binding-forms
    (λ (x) e #:refers-to x)
    (let ([x e_0]) e_1 #:refers-to x))
;; all functions curried, including + etc.

(define e? (redex-match? Λ e))
(define v? (redex-match? Λ v))
(define c? (redex-match? Λ c))
(define τ? (redex-match? Λ τ))
(define Σ? (redex-match? Λ Σ))
(define S? (redex-match? Λ S))

(module+ test
  (define t-sort (term (∀ (α) (→ (listof α) (→ (→ α (→ α bool)) (listof α))))))

  (test-case "rwdex-match"
    (check-pred e? (term (not TRUE)))
    (check-pred e? (term TRUE))
    (check-pred e? (term (let ([x 4]) x)))
    (check-pred e? (term (let ([x (f g)]) (h x))))

    (check-pred c? (term not))
    (check-pred c? (term 42))

    (check-pred v? (term TRUE))

    (check-pred τ? (term (listof α)))
    (check-pred τ? (term (→ α (→ α bool))))

    (check-pred Σ? t-sort)

    (check-pred S? (term ()))))

(define (Λ=? t0 t1)
  (alpha-equivalent? Λ t0 t1))

(define-judgment-form Λ
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
   --- App
   (free-variables (e_0 e_1) x*_2)])

(define-metafunction Λ
  free-variables# : e -> x*
  [(free-variables# e)
   x*
   (judgment-holds (free-variables e x*))]
  [(free-variables# e)
   ,(raise-user-error 'free-variables "undefined for ~a" (term e))])

(define-judgment-form Λ
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
     [(term TRUE)
      ==> (term ())]
     [(term (λ (x) x))
      ==> (term ())]
     [(term (λ (x) y))
      ==> (term (y))]
     [(term ((λ (x) y) (λ (x) z)))
      ==> (term (z y))]
     [(term ((λ (x) y) (λ (x) y)))
      ==> (term (y))])
  )
  (test-case "closed"
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term x)
      ==> #f]
     [(term (λ (x) y))
      ==> #f]
     [(term ((λ (x) y) TRUE))
      ==> #f]
     [(term (TRUE (λ (x) y)))
      ==> #f])
    (check-apply* (λ (t) (judgment-holds (closed ,t)))
     [(term FALSE)
      ==> #t]
     [(term (λ (x) TRUE))
      ==> #t]
     [(term ((λ (x) x) (λ (x) x)))
      ==> #t]))
)

(define-metafunction Λ
  δ : c v -> any
  [(δ not TRUE)
   FALSE]
  [(δ not FALSE)
   TRUE]
  [(δ not v)
   CHECK]
  [(δ add1 integer)
   ,(+ 1 (term integer))]
  [(δ add1 v)
   CHECK]
  [(δ first (one v_0 v_1))
   v_0]
  [(δ first none)
   ;; Section 2.3.1 : typeability does not require that first/rest are defined
   ;;  for values outside their domain
   CHECK]
  [(δ rest (one v_0 v_1))
   v_1]
  [(δ rest none)
   CHECK]
  [(δ c v)
   ;; aka, "untypable" Section 2.3
   UNDEFINED])
   ;;,(raise-user-error 'δ "undefined for ~a ~a" (term c) (term v))])

(module+ test
  (test-case "δ"
    (check-equal?
      (term #{δ not TRUE})
      (term FALSE))
    (check-equal?
      (term #{δ not FALSE})
      (term TRUE))
    (check-equal?
      (term #{δ not (λ (x) TRUE)})
      (term CHECK))
    (check-equal?
      (term #{δ add1 5})
      (term 6))
    (check-equal?
      (term #{δ first (one 1 none)})
      (term 1))
    (check-equal?
      (term #{δ first 4})
      (term UNDEFINED))
    (check-equal?
      (term #{δ rest (one 1 none)})
      (term none))
    (check-equal?
      (term #{δ rest none})
      (term CHECK))))

(define --->
  (reduction-relation Λ
   [--> (in-hole E ((λ (x) e) v))
        (in-hole E (substitute e x v))
        βv]
   [--> (in-hole E (c v_0))
        (in-hole E v_1)
        (where v_1 #{δ c v_0})
        δ_1]
   [--> (in-hole E (c v_0))
        CHECK
        (where CHECK #{δ c v_0})
        δ_2]
   [--> (in-hole E (let ([x v]) e))
        (in-hole E (substitute e x v))
        let]))

(define --->*
  (reflexive-transitive-closure/deterministic --->))

(module+ test
  (test-case "--->"
    (check-apply* --->*
     [(term ((λ (x) TRUE) FALSE))
      ==> (term TRUE)]
     [(term ((λ (x) x) FALSE))
      ==> (term FALSE)]
     [(term (not TRUE))
      ==> (term FALSE)]
     [(term (not FALSE))
      ==> (term TRUE)]
     [(term (not (λ (x) TRUE)))
      ==> (term CHECK)]
     [(term (add1 (add1 0)))
      ==> (term 2)]
     [(term (rest (one 5 none)))
      ==> (term none)]
     [(term (one (add1 0) (one (add1 1) none)))
      ==> (term (one 1 (one 2 none)))]
     [(term (let ([x (add1 2)]) (add1 x)))
      ==> (term 4)]))
)

(define-metafunction Λ
  eval : e -> a
  [(eval e)
   a
   (where a ,(--->* (term e)))])

;; "We say that a programming language that prevents programs from becoming
;;   stuck is _type safe_"

(define-metafunction Λ
  A-add : A [x ↦ Σ] -> A
  [(A-add A [x ↦ Σ])
   ((x_0 Σ_0) ... (x Σ) (x_2 Σ_2) ...)
   (where ((x_0 Σ_0) ... (x Σ_1) (x_2 Σ_2) ...) A)]
  [(A-add A [x ↦ Σ])
   ,(cons (term (x Σ)) (term A))])

(define-metafunction Λ
  A-ref : A x -> Σ
  [(A-ref A x)
   Σ
   (where ((x_0 Σ_0) ... (x Σ) (x_1 Σ_1) ...) A)])

(module+ test
  (test-case "A-add"
    (let ([A0 (term ())]
          [A1 (term ((a num)))]
          [A2 (term ((b (→ num num)) (a num)))]
          [A3 (term ((b (→ num num)) (a bool)))])
      (check-equal?
        (term #{A-add ,A0 [a ↦ num]})
        A1)
      (check-equal?
        (term #{A-add ,A1 [b ↦ (→ num num)]})
        A2)
      (check-equal?
        (term #{A-add ,A2 [a ↦ bool]})
        A3)
      (check-apply* (λ (t) (term #{A-ref ,A3 ,t}))
       [(term b)
        ==> (term (→ num num))]
       [(term a)
        ==> (term bool)]))))

(define-metafunction Λ
  typeOf : c -> τ
  [(typeOf integer)
   num]
  [(typeOf TRUE)
   bool]
  [(typeOf FALSE)
   bool]
  [(typeOf add1)
   (→ num num)]
  [(typeOf none)
   listof-num]
  [(typeOf first)
   (→ listof-num num)]
  [(typeOf rest)
   (→ listof-num listof-num)])

(module+ test
  (test-case "typeOf"
    (check-apply* (λ (t) (term #{typeOf ,t}))
     [(term 1)
      ==> (term num)]
     [(term 2)
      ==> (term num)]
     [(term TRUE)
      ==> (term bool)]
     [(term FALSE)
      ==> (term bool)]
     [(term add1)
      ==> (term (→ num num))])))

;; Lame-O
;; Rules require a stack of goal types
;;  and return the unused part of the stack
(define-judgment-form Λ
  #:mode (static-typing I I I O)
  #:contract (static-typing A e τ* τ*)
  [
   (where τ_0 #{typeOf c})
   --- const
   (static-typing A c (τ_0 τ_1 ...) (τ_1 ...))]
  [
   (side-condition ,(debug "λ checking ~a at ~a" (term (λ (x) e)) (term (→ τ_0 τ_1))))
   (static-typing #{A-add A [x ↦ τ_0]} e (τ_1 τ_2 ...) (τ_3 ...))
   --- lam
   (static-typing A (λ (x) e) ((→ τ_0 τ_1) τ_2 ...) (τ_3 ...))]
  [
   (static-typing A e_0 ((→ τ_1 τ_0) τ_2 ...) (τ_3 ...))
   (static-typing A e_1 (τ_1 τ_3 ...) (τ_4 ...))
   --- ap
   (static-typing A (e_0 e_1) (τ_0 τ_1 τ_2 ...) (τ_4 ...))]
  [
   (static-typing A e_0 (num τ_0 ...) (τ_1 ...))
   (static-typing A e_1 (listof-num τ_1 ...) (τ_2 ...))
   --- one
   (static-typing A (one e_0 e_1) (listof-num τ_0 ...) (τ_2 ...))]
  [
   (where Σ_poly #{A-ref A x})
   (where S #{unify τ_base Σ_poly})
   (side-condition ,(debug "unified ~a and ~a to ~a" (term τ_base) (term Σ_poly) (term S)))
   (instance τ_base S Σ_poly)
   --- id
   (static-typing A x (τ_base τ_1 ...) (τ_1 ...))]
  [
   (side-condition ,(debug "let-binding ~a" (term e_bnd)))
   (static-typing A_0 e_bnd (τ_bnd τ_0 ...) (τ_1 ...))
   (where A_1 #{A-add A_0 [x ↦ #{close τ_bnd A_0}]})
   (side-condition ,(debug "let-binding ~a, generalized type to ~a" (term e_bnd) (term #{A-ref A_1 x})))
   (static-typing A_1 e_bdy (τ_bdy τ_1 ...) (τ_2 ...))
   --- let
   (static-typing A_0 (let ([x e_bnd]) e_bdy) (τ_bdy τ_bnd τ_0 ...) (τ_2 ...))])

(define-metafunction Λ
  static-typing# : e τ* -> boolean
  [(static-typing# e τ*)
   #true
   (judgment-holds (static-typing () e τ* ()))]
  [(static-typing# e τ*)
   ,(raise-user-error 'static-typing "unused types ~a" (term τ*_1))
   (judgment-holds (static-typing () e τ* τ*_1))]
  [(static-typing# e τ*)
   #false])
   ;;,(raise-user-error 'static-typing "undefined for ~a ~a" (term e) (term τ*))])

(module+ test
  (test-case "static-typing"
    (let ([e (term ((λ (x) (add1 x)) 0))]
          [τ* (term (num num num))])
      (check-true (term #{static-typing# ,e ,τ*})))
    (check-false
      (term #{static-typing# (1 2) (num num)}))
    (check-true
      (term #{static-typing#
        (λ (x) (first (rest x)))
        ((→ listof-num num) listof-num listof-num)}))
    (check-true
      (term #{static-typing#
        ((λ (x) (first (rest x)))
         none)
        (num listof-num listof-num listof-num)}))
    (check-true
      (term #{static-typing#
        (λ (y) y)
        ((→ α α))}))
    (check-false
      (term #{static-typing#
        (λ (y) y)
        ((→ num bool))}))
    (check-true
      (term #{static-typing#
        (let ([x (λ (y) y)])
          (let ([z (x 1)])
            (x none)))
        (listof-num (→ α α) num num listof-num)})))
)

;; "This condition requires that for a typable application `(c v)`,
;;  `δ(c,v)` must be defined and yield either a value of the result type of `c`
;;  or a **check**"
;;
;; Not sure when we'll use this (in --->* ?), so it's simple for now
(define-judgment-form Λ
  #:mode (typeable I)
  #:contract (typeable e)
  [
   (where (→ τ_0 τ_1) #{typeOf c})
   (where #true #{static-typing# v (τ_0)})
   (where v_1 #{δ c v})
   (where #true #{static-typing# v_1 (τ_1)})
   --- i
   (typeable (c v))]
  [
   (where (→ τ_0 τ_1) #{typeOf c})
   (where #true #{static-typing# v (τ_0)})
   (where CHECK #{δ c v})
   --- ii
   (typeable (c v))])

(module+ test
  (test-case "typeable"
    (check-true* (λ (t) (judgment-holds (typeable ,t)))
     [(term (add1 3))]
     [(term (first (one 1 none)))]
     [(term (first none))])

    (check-false* (λ (t) (judgment-holds (typeable ,t)))
     [(term (add1 TRUE))]
     [(term (TRUE TRUE))]
     [(term (first 3))])))

(define-judgment-form Λ
  #:mode (FV I O)
  [
   (FV τ α*_1)
   (where α*_2 ,(set-subtract (term α*_1) (term α*_0)))
   --- Σ
   (FV (∀ α*_0 τ) α*_2)]
  [
   (FV τ_0 (α_0 ...))
   (FV τ_1 (α_1 ...))
   --- →
   (FV (→ τ_0 τ_1) (α_0 ... α_1 ...))]
  [
   --- τ-base
   (FV τ-base ())]
  [
   (FV τ α*)
   --- listof
   (FV (listof τ) α*)]
  [
   --- α
   (FV α (α))])

(define-metafunction Λ
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
     [(term num)
      ==> (term ())]
     [(term (∀ () num))
      ==> (term ())]
     [(term (∀ (α) (listof α)))
      ==> (term ())]
     [(term (listof α))
      ==> (term (α))]
     [(term (→ α β))
      ==> (term (α β))]
     [(term (∀ (α) (→ α β)))
      ==> (term (β))]
     [t-sort
      ==> (term ())])))

(define-metafunction Λ
  S-ref : S α -> τ
  [(S-ref S x)
   τ
   (where ((x_0 τ_0) ... (x τ) (x_1 τ_1) ...) S)]
  [(S-ref S x)
   x])

(define-judgment-form Λ
  #:mode (tsubst I I O)
  #:contract (tsubst τ S τ)
  [
   --- τ-base
   (tsubst τ-base S τ-base)]
  [
   (tsubst τ_0 S τ_2)
   (tsubst τ_1 S τ_3)
   --- →
   (tsubst (→ τ_0 τ_1) S (→ τ_2 τ_3))]
  [
   (tsubst τ_0 S τ_1)
   --- listof
   (tsubst (listof τ_0) S (listof τ_1))]
  [
   ;; NOTE: [τ = α] if unbound in S
   (where τ #{S-ref S α})
   --- α
   (tsubst α S τ)])

(define-metafunction Λ
  tsubst# : τ S -> τ
  [(tsubst# τ S)
   τ_1
   (judgment-holds (tsubst τ S τ_1))]
  [(tsubst# τ S)
   ,(raise-user-error 'tsubst "undefined for ~a" (term τ) (term S))])

(module+ test
  (test-case "tsubst"
    (let ([S (term ((α num) (β bool) (γ (→ listof-num num)) (d num)))])
      (check-apply* (λ (t) (term #{tsubst# ,t ,S}))
       [(term num)
        ==> (term num)]
       [(term (→ num listof-num))
        ==> (term (→ num listof-num))]
       [(term (→ α num))
        ==> (term (→ num num))]
       [(term (→ β γ))
        ==> (term (→ bool (→ listof-num num)))]))))

(define-metafunction Λ
  A-cod : A -> Σ*
  [(A-cod A)
   (Σ ...)
   (where ((α Σ) ...) A)])

(define-metafunction Λ
  S-dom : S -> α*
  [(S-dom S)
   (α ...)
   (where ((α τ) ...) S)])

;; TODO \E or τ
(define-judgment-form Λ
  #:mode (instance I I I)
  #:contract (instance τ S Σ)
  [
   (where #true ,(set=? (term α*) (term #{S-dom S})))
   (tsubst τ_1 S τ_0)
   ---
   (instance τ_0 S (∀ α* τ_1))]
  [
   ---
   (instance τ S τ)])

(module+ test
  (test-case "instance"
    (check-true (judgment-holds
      (instance num () num)))
    (check-true (judgment-holds
      (instance num () (∀ () num))))
    (check-true (judgment-holds
      (instance (→ num num) ((α num)) (∀ (α) (→ α α)))))
    (check-true (judgment-holds
      (instance (→ (listof num) (→ (→ num (→ num bool)) (listof num)))
                ((α num))
                ,t-sort)))
    (check-false (judgment-holds
      (instance num ((α num)) (∀ (α) (→ α α)))))
    (check-false (judgment-holds
      (instance (→ num num) () (∀ (α) (→ α α)))))
    (check-false (judgment-holds
      (instance (→ num num) ((α num) (β num)) (∀ (α) (→ α α)))))))

;; Figure 2.4
;;  technically α* only needs to be a subset of the difference
(define-metafunction Λ
  close : τ A -> Σ
  [(close τ A)
   ,(if (null? (term α*))
      (term τ)
      (term (∀ α* τ)))
   (where α*_τ #{FV# τ})
   (where α*_A #{FV# A})
   (where α* ,(set-subtract (term α*_τ) (term α*_A)))])

(module+ test
  (test-case "close"
    (check-apply* (λ (t) (term #{close ,(car t) ,(cadr t)}))
     [(term [num ()])
      ==> (term num)]
     [(term [α ()])
      ==> (term (∀ (α) α))]
     [(term [α ((x (→ num α)))])
      ==> (term α)]
     [(term [(→ α β) ((q num) (r num) (s β))])
      ==> (term (∀ (α) (→ α β)))]))
)

;; TODO do correctly
(define-metafunction Λ
  unify : Σ Σ -> any
  [(unify (∀ α* τ) Σ)
   #{unify τ Σ}]
  [(unify Σ (∀ α* τ))
   #{unify Σ τ}]
  [(unify α τ)
   ((α τ))]
  [(unify τ α)
   ((α τ))]
  [(unify α τ)
   ((α τ))]
  [(unify τ-base τ-base)
   ()]
  [(unify (→ τ_0 τ_1) (→ τ_2 τ_3))
   ,(set-union (term S_0) (term S_1))
   (where S_0 #{unify τ_0 τ_2})
   (where S_1 #{unify τ_1 τ_3})]
  [(unify τ_0 τ_1)
   UNIFY-ERROR])

(module+ test
  (test-case "unify"
    (check-apply* (λ (t) (term #{unify ,(car t) ,(cadr t)}))
     [(term [num num])
      ==> (term ())]
     [(term [num bool])
      ==> (term UNIFY-ERROR)]
     [(term [num (→ num num)])
      ==> (term UNIFY-ERROR)]
     [(term [(→ α β) (→ num num)])
      ==> (term ((β num) (α num)))]
     [(term [(→ α β) (→ num bool)])
      ==> (term ((β bool) (α num)))]
     [(term [(∀ (α β) (→ α β)) (→ num bool)])
      ==> (term ((β bool) (α num)))]))
)

