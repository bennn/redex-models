#lang mf-apply racket/base

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

;; =============================================================================
;; === Section 3: Symbolic Heaps

;; SH is the set of all symbolic heaps, not really the name of the language but whatever.
(define-language SH
  [Heap ::= ((Loc Val) ...)]
  [Stack ::= ((x Val) ...)]
  [State ::= (Heap Stack)]
  [E ::= ;; expressions
         x
         (t E ...)]
  [t ::= ;; term constructors
         A B C
         cons]
  [Π ::= ;; pure formulae
         (E = E)
         (E ≠ E)
         true
         (Π ∧ Π)]
  [B ::= ;; base spatial predicates
         (E ↦ E) ; x points-to y
         (lseg E E)] ; list segment from x to y
  [Σ ::= ;; spatial formulae
         B
         true
         emp
         (Σ * Σ)]
  [Δ ::= (Π ∧ Σ)]
  [H ::= (∃ (a ...) Δ)]
  ;; --------------------------------------------------------------------------
  [x y z a b c ::= ;; xyz = program var, abc = logical var
                   (variable-not-otherwise-mentioned)]
  ;;#:binding-forms
  ;;  (∃ (a ...) Δ #:refers-to (a ...))
)

(define Heap? (redex-match? SH Heap))
(define Stack? (redex-match? SH Stack))
(define State? (redex-match? SH State))
(define E? (redex-match? SH E))
(define t? (redex-match? SH t))
(define Π? (redex-match? SH Π))
(define B? (redex-match? SH B))
(define Σ? (redex-match? SH Σ))
(define Δ? (redex-match? SH Δ))
(define H? (redex-match? SH H))

(define-metafunction SH
  *# : any any -> any
  [(*# Δ_1 Δ_2)
   ((Π_1 ∧ Π_2) ∧ (Σ_1 * Σ_2))
   (where (Π_1 ∧ Σ_1) Δ_1)
   (where (Π_2 ∧ Σ_2) Δ_2)]
  [(*# H_1 H_2)
   (∃ (a_1 ... a_2 ...) #{*# Δ_1 Δ_2})
   (where (∃ (a_1 ...) Δ_1) H_1)
   (where (∃ (a_2 ...) Δ_2) H_2)]
  [(*# Δ_1 Σ_2)
   (Π_1 ∧ (Σ_1 * Σ_2))
   (where (Π_1 ∧ Σ_1) Δ_1)]
  [(*# H_1 Σ_2)
   (∃ (a_1 ...) #{*# Δ_1 Σ_2})
   (where (∃ (a_1 ...) Δ_1) H_1)])

(define-metafunction SH
  ∧# : Π any -> any
  [(∧# Π_1 Δ_2)
   ((Π_1 ∧ Π_2) ∧ Σ_2)
   (where (Π_2 ∧ Σ_2) Δ_2)]
  [(∧# Π_1 H_2)
   (∃ (a_2 ...) #{∧# Π Δ_2})
   (where (∃ (a_2 ...) Δ_2) H_2)])

(module+ test
  (let* ([Π0 (term true)]
         [Σ0 (term emp)]
         [Δ0 (term (,Π0 ∧ ,Σ0))]
         [H0 (term (∃ (a a) ,Δ0))])
    (check-pred Π? Π0)
    (check-pred Σ? Σ0)
    (check-pred Δ? Δ0)
    ;(check-pred H? H0) ;; TODO
    (test-case "*#:based"
      (check-apply* (λ (t) (term #{*# ,(car t) ,(cadr t)}))
       [(list Δ0 Δ0)
        ==> (term ((,Π0 ∧ ,Π0) ∧ (,Σ0 * ,Σ0)))]
       ;; H H
       ;; Δ Σ
       ;; H Σ
       ;[(term [A B])]
      )
    )
    (test-case "∧#"
       ;; Π Δ
       ;; Π H
    ))
)

;; -----------------------------------------------------------------------------
;; Section 4: Abduction for Separated Heap Abstractions
