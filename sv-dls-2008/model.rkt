#lang mf-apply racket/base

;; Q. is gradual typing compatible with type inference?
;;    either HM, dataflow-based, soft typing, local, ....

;; Contributions of this paper:
;; - explore design space, 3 non-starter ideas
;;   1. treat dynamic types as type variables
;;   2. check well-typed after substitution
;;   3. ignore dynamic types after unification
;; - new type system, prove it satisfies criteria
;; - inference for new type system,
;;   does not infer types that add unnecessary casts

;; TODO
;; - does the paper have recursive functions?

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs/redex))

;; =============================================================================

(define-language λ?
  [γ ::= ;; ground types
         Bool Int Unit]
  [c ::= ;; constants
         true false succ Z null (fix τ)]
  [τ ::= ;; types
         α ? γ (τ → τ)]
  [e ::= x c (e e) (λ (x : τ) e)]
  [e+ ::= x c (e+ e+) (λ (x : τ) e+) (λ (x) e+) (let ((x : τ) e+) e+)]
  [Γ ::= ((x τ) ...)]
  [S ::= Γ]
  [α x y ::= variable-not-otherwise-mentioned]
  #:binding-forms (λ (x : τ) e #:refers-to x))

(define γ? (redex-match? λ? γ))
(define c? (redex-match? λ? c))
(define τ? (redex-match? λ? τ))
(define e? (redex-match? λ? e))
(define e+? (redex-match? λ? e+))
(define Γ? (redex-match? λ? Γ))

(define (λ?= t0 t1)
  (alpha-equivalent? λ? t0 t1))

(module+ test
  (test-case "redex-match"
    (check-pred e+? (term (let ((x : Int) Z) (succ x))))
    ))

(define-judgment-form λ?
  #:mode (desugar I O)
  #:contract (desugar e+ e)
  [
   --- Var
   (desugar x x)]
  [
   --- C
   (desugar c c)]
  [
   (desugar e+_0 e_0)
   (desugar e+_1 e_1)
   --- App
   (desugar (e+_0 e+_1) (e_0 e_1))]
  [
   (desugar e+ e)
   --- λτ
   (desugar (λ (x : τ) e+) (λ (x : τ) e))]
  [
   (desugar e+ e)
   --- λ
   (desugar (λ (x) e+) (λ (x : ?) e))]
  [
   (desugar e+_0 e_0)
   (desugar (λ (x : τ) e+_1) e)
   --- let
   (desugar (let ((x : τ) e+_0) e+_1) (e e_0))])

(define-metafunction λ?
  [(desugar# e+)
   e
   (judgment-holds (desugar e+ e))]
  [(desugar# e+)
   ,(raise-user-error 'desugar "undefined for ~a" (term e+))])

(module+ test
  (test-case "desugar"
    (check λ?=
      (term #{desugar# (let ((x : Int) Z) (succ x))})
      (term ((λ (x : Int) (succ x)) Z)))
    (check λ?=
      (term #{desugar# ((λ (x) Z) Z)})
      (term ((λ (x : ?) Z) Z)))))

(define-metafunction λ?
  lookup : Γ x -> τ
  [(lookup Γ x)
   τ
   (where ((x_0 τ_0) ... (x τ) (x_1 τ_1) ...) Γ)]
  [(lookup Γ x)
   ,(raise-user-error 'lookup "unbound variable ~a in environment ~a" (term x) (term Γ))])

(define-metafunction λ?
  typeof : c -> τ
  [(typeof true)
   Bool]
  [(typeof false)
   Bool]
  [(typeof Z)
   Int]
  [(typeof succ)
   (Int → Int)]
  [(typeof null)
   Unit]
  [(typeof (fix τ))
   τ]
  [(typeof c)
   ,(raise-user-error 'typeof "undefined for ~a" (term c))])

(define-metafunction λ?
  extend : Γ (x ↦ τ) -> Γ
  [(extend Γ (x ↦ τ))
   ((x τ) (x_0 τ_0) ... (x_2 τ_2) ...)
   (where ((x_0 τ_0) ... (x τ_1) (x_2 τ_2) ...) Γ)]
  [(extend Γ (x ↦ τ))
   ,(cons (term (x τ)) (term Γ))])

(module+ test
  (test-case "env-metafunctions"
  )
)

(define-judgment-form λ?
  #:mode (⊢g I I O)
  #:contract (⊢g Γ e τ)
  [
   (where τ #{lookup Γ x})
   --- Var
   (⊢g Γ x τ)]
  [
   (where τ #{typeof c})
   --- Cnst
   (⊢g Γ c τ)]
  [
   (⊢g Γ e_1 ?)
   (⊢g Γ e_2 τ)
   --- App1
   (⊢g Γ (e_1 e_2) ?)]
  [
   (⊢g Γ e_1 (τ_1 → τ_3))
   (⊢g Γ e_2 τ_2)
   (~ τ_1 τ_2)
   --- App2
   (⊢g Γ (e_1 e_2) τ_3)]
  [
   (⊢g #{extend Γ (x ↦ τ_1)} e τ_2)
   --- Abs
   (⊢g Γ (λ (x : τ_1) e) (τ_1 → τ_2))])

(define-judgment-form λ?
  #:mode (~ I I)
  #:contract (~ τ τ)
  [
   --- Ground
   (~ γ γ)]
  [
   --- ?L
   (~ ? τ)]
  [
   --- ?R
   (~ τ ?)]
  [
   (~ τ_3 τ_1)
   (~ τ_2 τ_4)
   --- →
   (~ (τ_1 → τ_2) (τ_3 → τ_4))])

(module+ test
  (test-case "type consistency"
    (check-apply* values
     [(judgment-holds (~ Int Int))
      ==> #t]
     [(judgment-holds (~ Bool Int))
      ==> #f]
     [(judgment-holds (~ ? Int))
      ==> #t]
     [(judgment-holds (~ Int ?))
      ==> #t]
     [(judgment-holds (~ ? (Int → Bool)))
      ==> #t]
     [(judgment-holds (~ (Int → ?) (? → Int)))
      ==> #t]
     [(judgment-holds (~ (Int → ?) (Int → Bool)))
      ==> #t]
     [(judgment-holds (~ (Int → ?) (Bool → ?)))
      ==> #f]
     [(judgment-holds (~ (Int → Int) (Int → Bool)))
      ==> #f]))

  (test-case "well-typed"
    (check-true* values
     [(judgment-holds (⊢g ((x Int)) x Int))]
     [(judgment-holds (⊢g () true Bool))]
     [(judgment-holds (⊢g ((x Int)) false Bool))]
     [(judgment-holds (⊢g ((x Int)) Z Int))]
     [(judgment-holds (⊢g () null Unit))]
     [(judgment-holds (⊢g () (succ Z) Int))]
     [(judgment-holds (⊢g ((f (Int → Int))) (f Z) Int))]
     [(judgment-holds (⊢g ((f ?) (x Int)) (f x) ?))]
     [(judgment-holds (⊢g () (λ (x : Int) x) (Int → Int)))]
     [(judgment-holds (⊢g ((y Bool)) ((λ (x : ?) y) (succ Z)) Bool))])
  )
)

;; -----------------------------------------------------------------------------
;; New type system, consistent equal, consistent less

(define-judgment-form λ?
  #:mode (~= I I I)
  #:contract (~= S τ τ)
  [
   --- CEG
   (~= S γ γ)]
  [
   --- CEDL
   (~= S ? τ)]
  [
   --- CEDR
   (~= S τ ?)]
  [
   (~= S τ_1 τ_3)
   (~= S τ_2 τ_4)
   --- CEFUN
   (~= S (τ_1 → τ_2) (τ_3 → τ_4))]
  [
   (⊑ S τ #{lookup S α})
   --- CEVL
   (~= S α τ)]
  [
   (⊑ S τ #{lookup S α})
   --- CEVR
   (~= S τ α)])

(define-judgment-form λ?
  #:mode (⊑ I I I)
  #:contract (⊑ S τ τ)
  [
   (where τ #{lookup S α})
   --- CLVar
   (⊑ S α τ)]
  [
   --- CLG
   (⊑ S γ γ)]
  [
   --- CLDL
   (⊑ S ? τ)]
  [
   (⊑ S τ_1 τ_3)
   (⊑ S τ_2 τ_4)
   --- CLFun
   (⊑ S (τ_1 → τ_2) (τ_3 → τ_4))])

(module+ test
  (test-case "~="
    (check-true* values
     [(judgment-holds (~= () Int Int))]
     [(judgment-holds (~= () ? Int))]
     [(judgment-holds (~= () ? (Int → Bool)))]
     [(judgment-holds (~= () (Int → Int) (Int → Int)))]
     [(judgment-holds (~= ((α Int)) α Int))]
     [(judgment-holds (~= ((α Int)) Int α))]
     [(judgment-holds (~= ((α ((? → Bool) → (Int → Bool)))
                           (β (? → Bool)))
                          (Int → α)
                          (? → (β → (Int → ?)))))])
    (check-false* values
     [(judgment-holds (~= () Int Bool))])
  )
  (test-case "⊑"
    (check-true* values
     [(judgment-holds (⊑ ((α Int)) α Int))]
     [(judgment-holds (⊑ () Int Int))]
     [(judgment-holds (⊑ () ? Int))]
     [(judgment-holds (⊑ () ? (Int → Int)))]
     [(judgment-holds (⊑ () (Int → Int) (Int → Int)))])
  )
)

(define-metafunction λ?
  fresh : S -> α
  [(fresh ((α τ) ...))
   ,(string->symbol (format "α~a" (length (term (α ...)))))])

(define-judgment-form λ?
  #:mode (⊢α I I I O)
  #:contract (⊢α S Γ e τ)
  [
   (where τ #{lookup Γ x})
   --- GVar
   (⊢α S Γ x τ)]
  [
   (where τ #{typeof c})
   --- GCnst
   (⊢α S Γ c τ)]
  [
   (⊢α S Γ e_1 τ_1)
   (⊢α S Γ e_2 τ_2)
   (where α #{fresh S})
   (~= S τ_1 (τ_2 → α))
   --- GApp
   (⊢α S Γ (e_1 e_2) α)]
  [
   (⊢α S #{extend Γ [x ↦ τ_1]} e τ_2)
   --- GAbs
   (⊢α S Γ (λ (x : τ_1) e) (τ_1 → τ_2))])

;; TODO ~= rules need to output a new S

#;(module+ test
  (test-case "⊢α"
    (check-true* values
     [(judgment-holds (⊢α () () (succ Z) Int))]
    )
  )
)