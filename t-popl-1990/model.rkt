#lang mf-apply racket/base

(require
  redex/reduction-semantics
  racket/set)

(module+ test
  (require rackunit)
  (define-syntax-rule (check-judgment-holds t ...)
    (check-true (judgment-holds t ...)))
  (define-syntax-rule (check-judgment-fails t ...)
    (check-false (judgment-holds t ...))))

;; =============================================================================

(define-language Church
  [τ ::= Int Bool (→ τ τ) (× τ τ) Dyn] ;; Dyn = Ω
  [e ::= x v (δ e) (cons e e) (e e)]
  [v ::= boolean integer (λ (x : τ) e)]
  [i ::= x boolean integer (λ (x : τ) i) (cons i i) (δ i) (i i) (i τ ↑ τ) (i τ ↓ τ)]
  [δ ::= cons first second]
  [Γ ::= ((x τ) ...)]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms (λ (x : τ) e #:refers-to x))

(define τ? (redex-match? Church τ))
(define e? (redex-match? Church e))
(define v? (redex-match? Church v))
(define i? (redex-match? Church i))
(define δ? (redex-match? Church δ))

;; The order relates all (and only) pairs (≤ τ_1 τ_2)
;; such that an object x of type τ_1 can be converted to one
;; of type τ_2 by applying or composing tagging operations.
(define-judgment-form Church
  #:mode (≤ I I)
  #:contract (≤ τ τ)
  [
   ---
   (≤ τ τ)]
  [
   ---
   (≤ τ Dyn)]
  [
   (≤ τ_0 τ_2)
   (≤ τ_1 τ_3)
   ---
   (≤ (→ τ_0 τ_1) (→ τ_2 τ_3))]
  [
   (≤ τ_0 τ_2)
   (≤ τ_1 τ_3)
   ---
   (≤ (× τ_0 τ_1) (× τ_2 τ_3))])

(module+ test
  (test-case "≤"
    (check-judgment-holds (≤ Int Int))
    (check-judgment-holds (≤ Int Dyn))
    (check-judgment-holds (≤ Dyn Dyn))
    (check-judgment-holds (≤ Int Dyn))
    (check-judgment-holds (≤ (× Int Int) (× Dyn Dyn)))
    (check-judgment-holds (≤ (× Dyn Int) (× Dyn Dyn)))
    (check-judgment-holds (≤ (× Dyn Int) (× Dyn Int)))
    (check-judgment-holds (≤ (→ Int Int) (→ Dyn Dyn)))
    (check-judgment-holds (≤ (→ Dyn Int) (→ Dyn Dyn)))
    (check-judgment-holds (≤ (→ Dyn Int) (→ Dyn Int)))

    (check-judgment-fails (≤ Dyn Int))
    (check-judgment-fails (≤ Int Bool))))

(define-judgment-form Church
  #:mode (valid-casts I)
  #:contract (valid-casts i)
  [
   ---
   (valid-casts x)]
  [
   ---
   (valid-casts integer)]
  [
   ---
   (valid-casts boolean)]
  [
   (valid-casts i)
   ---
   (valid-casts (λ (x : τ) i))]
  [
   (valid-casts i_0)
   (valid-casts i_1)
   ---
   (valid-casts (cons i_0 i_1))]
  [
   (valid-casts i)
   ---
   (valid-casts (δ i))]
  [
   (valid-casts i_0)
   (valid-casts i_1)
   ---
   (valid-casts (i_0 i_1))]
  [
   (≤ τ_0 τ_1)
   (valid-casts i)
   ---
   (valid-casts (i τ_0 ↑ τ_1))]
  [
   (≤ τ_1 τ_0)
   (valid-casts i)
   ---
   (valid-casts (i τ_0 ↓ τ_1))])

(module+ test
  (define emb-nat (term (λ (x : Int) (x Int ↑ Dyn))))
  (define l (term (cons 2 2)))
  (define l3 (term (l (× Int Int) ↑ Dyn)))
  (define l4 (term (cons (,emb-nat (first ,l)) (,emb-nat (second ,l)))))

  (check-pred i? l)
  (check-pred i? l3)
  (check-pred i? l4))

(define-judgment-form Church
  #:mode (⊢ I I O O)
  #:contract (⊢ Γ e i τ)
  [
   (where ((x_0 τ_0) ... (x τ) (x_1 τ_1) ...) Γ)
   ---
   (⊢ Γ x x τ)]
  [
   (⊢ Γ e i τ)
   (side-condition ,(not (equal? (term τ) (term Dyn))))
   (≤ τ Dyn) ;; could be any supertype, not just Dyn
   ---
   (⊢ Γ e (i τ ↑ Dyn) Dyn)]
  [
   (where ((x_0 τ_0) ...) Γ)
   (where Γ_0 ((x τ) (x_0 τ_0) ...))
   (⊢ Γ_0 e i τ_1)
   ---
   (⊢ Γ (λ (x : τ) e) (λ (x : τ) i) (→ τ τ_1))]
  [
   (⊢ Γ e_0 i_0 τ_0)
   (⊢ Γ e_1 i_1 τ_1)
   ---
   (⊢ Γ (cons e_0 e_1) (cons i_0 i_1) (× τ_0 τ_1))]
  [
   (⊢ Γ e_f i_f (→ τ_0 τ_1))
   (⊢ Γ e_a i_a τ_2)
   (≤ τ_0 τ_2)
   ---
   (⊢ Γ (e_f e_a) (i_f (i_a τ_0 ↓ τ_2)) τ_2)]
  [
   (⊢ Γ e_f i_f Dyn)
   (⊢ Γ e_a i_a τ)
   ---
   (⊢ Γ (e_f e_a) ((i_f (→ τ Dyn) ↓ Dyn) i_a) Dyn)]
  [
   (⊢ Γ e_f i_f (→ τ_0 τ_1))
   (⊢ Γ e_a i_a τ_2)
   ---
   (⊢ Γ (e_f e_a) ((i_f (→ τ_2 τ_1) ↓ (→ τ_0 τ_1)) i_a) τ_1)])

;; infinite loop?
;(module+ test
;  (test-case "fix"
;    (check-judgment-holds (⊢ () (λ (f : (→ Dyn Dyn))
;                                  ((λ (x : Dyn) (λ (z : Dyn) ((f (x x)) z)))
;                                   (λ (x : Dyn) (λ (z : Dyn) ((f (x x)) z)))))
;                                (λ (f : (→ Dyn Dyn))
;                                  ((λ (x : Dyn) (λ (z : Dyn) (((f ((x (→ Dyn Dyn) ↓ Dyn) x)) (→ Dyn Dyn) ↓ Dyn) z)))
;                                   ((λ (x : Dyn) (λ (z : Dyn) (((f ((x (→ Dyn Dyn) ↓ Dyn) x)) (→ Dyn Dyn) ↓ Dyn) z))) (→ Dyn (→ Dyn Dyn)) ↑ Dyn)))
;                                (→ (→ Dyn Dyn) (→ Dyn Dyn))))))
