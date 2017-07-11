#lang racket/base

;; Notes from Mike Fagan's dissertation
;;  see `./src/f-diss-1991.pdf`

(require
  redex/reduction-semantics
  racket/set)

;; =============================================================================

(define-language RT
  [F ::= ;; set of function symbols
         f0 f1 f2 f3 f4 f5 f6 f7 f8 f9]
  [Σ ::= ;; terms, technically Σ(F,X)
         X F (F Σ ...)]
  [RTE ::= ;; regular tree expressions, technically R(F,X)
           ∅ x F (F RTE ...) (+ RTE RTE) (** X RTE)]
  [A ::= ((X σ) ...)]
  [σ ::= TYPES]
  [τ ::= TYPES]
  [S ::= ((X σ) ...)] ;; substitutions
  [X ::= variable-not-otherwise-mentioned])

(define-metafunction RT
  arity : F -> natural
  [(arity F)
   (string->number (substring (symbol->string (term F)) 1))])

(define-judgment-form RT
  #:mode (well-formed-term I)
  #:contract (well-formed-term Σ)
  [
   --- Var
   (well-formed-term X)]
  [
   (where 0 #{arity F})
   --- Constant
   (well-formed-term F)]
  [
   (side-condition ,(= (term #{arity F}) (length (term (Σ ...)))))
   (well-formed-term Σ) ...
   --- App
   (well-formed-term (F Σ ...))])

;; Definition 2.11
(define-judgment-form RT
  #:mode (well-formed I)
  #:contract (well-formed RTE)
  [
   --- Var
   (well-formed X)]
  [
   (where 0 #{arity F})
   --- Constant
   (well-formed F)]
  [
   (side-condition ,(= (term #{arity F}) (length (term (RTE ...)))))
   (well-formed RTE) ...
   --- App
   (well-formed (F RTE ...))]
  [
   (well-formed RTE_0)
   (well-formed RTE_1)
   --- Union
   (well-formed (+ RTE_0 RTE_1))]
  [
   (well-formed RTE)
   --- Star
   (well-formed (** X RTE))])

;; "Terms" & "Trees" are synonyms here

;; -----------------------------------------------------------------------------
;; (stopped typing so much, save my hands)

;; Definition 2.12 _set of grafts_
;;  apply `f ∈ F` to list of sets of terms
;;  kinda like AbsInt

;; Definition 2.13 substitution

;; Definition 2.14 kleene closure
;;  (substitute the variable X in `(** X RTE)` for ∅, RTE[X ↦ ∅], RTE[X ↦ RTE[X ↦ ∅]], ...

;; Definition 2.15 terms of an RTE

;; Theorem 2.1 _Decidability of Emptyness, Finiteness, Subset_

;; Definition 2.16 regular types

;; Definition 2.17 formal contractiveness

(define-judgment-form RT
  #:mode (contractive-in I I)
  #:contract (contractive-in X RTE)
  [
   (where 0 #{arity F})
   --- Constant
   (contractive-in X F)]
  [
   (side-condition ,(not (equal? (term X_0) (term X_1))))
   --- Var
   (contractive-in X_0 X_1)]
  [
   --- App
   (contractive-in X (F RTE ...))]
  [
   (contractive-in X RTE_0)
   (contractive-in X RTE_1)
   --- Union
   (contractive-in X (+ RTE_0 RTE_1))])

;; Section 2.5.3 : semantic interpretation of types is congruent with subtyping relation

;; Definition 2.30 : typing rules, with a Sub rule

;; TODO test such things

;; =============================================================================
;; Chapter 3 notes

(define-language ML ;; Milner's language
  [A ::= ((x σ) ...)]
  [τ ::= α (→ τ τ) Int]
  [σ ::= τ (∀ α σ)]
  [e ::= x (λ x e) (e e) (let [x e] e)]
  [x* ::= (x ...)]
  [α* ::= (α ...)]
  [x α ::= variable-not-otherwise-mentioned]
  #:binding-forms (λ x e #:refers-to x)
                  (let [x e_0] e_1 #:refers-to x))

(define-judgment-form ML
  #:mode (infer-type I I O)
  #:contract (infer-type A e τ)
  [
   (where σ #{A-ref A x})
   --- Taut
   (infer-type A x σ)]
  [
   (infer-type A x σ_1)
   (infer-instance σ_0 σ_1)
   --- Inst
   (infer-type A x σ_0)]
  [
   (infer-type A e σ)
   (choose-variable α)
   (side-condition ,(not (member (term α) (term #{FV# A}))))
   --- Gen
   (infer-type A e (∀ α σ))]
  [
   (choose-type τ_0)
   (infer-type #{A-add A x τ_0} e τ_1)
   --- Abst
   (infer-type A (λ x e) (→ τ_0 τ_1))]
  [
   (infer-type A e_0 (→ τ_1 τ_2))
   (infer-type A e_1 τ_1)
   --- App
   (infer-type A (e_0 e_1) τ_2)]
  [
   (infer-type A e_0 τ_0)
   (infer-type #{A-add A x τ_0} e_1 τ_1)
   --- Let
   (infer-type A (let [x e_0] e_1) τ_1)])

(define-judgment-form ML
  #:mode (choose-type O)
  #:contract (choose-type σ)
  [
   --- yolo
   (choose-type Int)])

(define-judgment-form ML
  #:mode (choose-variable O)
  #:contract (choose-variable σ)
  [
   --- yolo
   (choose-variable α9)])

;; Given `σ_1`, infer a `σ_0` such that `σ_0 < σ_1`
(define-judgment-form ML
  #:mode (infer-instance O I)
  #:contract (infer-instance σ σ)
  [
   --- FAIL
   (infer-instance σ σ)])

(define-metafunction ML
  A-add : A x σ -> A
  [(A-add A x σ)
   ((x_0 σ_0) ... (x σ) (x_2 σ_2) ...)
   (where ((x_0 σ_0) ... (x σ_1) (x_2 σ_2) ...) A)]
  [(A-add A x σ)
   ((x σ) (x_0 σ_0) ...)
   (where ((x_0 σ_0) ...) A)])

(define-metafunction ML
  A-ref : A x -> σ
  [(A-ref A x)
   σ
   (where ((x_0 σ_0) ... (x σ) (x_1 σ_1) ...) A)])

(define-metafunction ML
  FV# : any -> α*
  [(FV# σ)
   x*
   (judgment-holds (FV σ x*))]
  [(FV# ())
   ()]
  [(FV# ((x σ) (x_1 σ_1) ...))
   ,(set-union (term α*) (term #{FV# ((x_1 σ_1) ...)}))
   (judgment-holds (FV σ x*))])

(define-judgment-form ML
  #:mode (FV I O)
  #:contract (FV σ α*)
  [
   (FV σ α*)
   --- ∀
   (FV (∀ α σ) ,(set-remove (term α*) (term α)))]
  [
   (FV τ_0 α*_0)
   (FV τ_1 α*_1)
   --- →
   (FV (→ τ_0 τ_1) ,(set-union (term α*_0) (term α*_1)))]
  [
   --- Int
   (FV Int ())]
  [
   --- α
   (FV α (α))])

;; Definition 3.1 : Algorithm W
;;  (pretty simple, makes sense how to adapt this to SoftTypes,
;;   not so sure about Unification)

;(define-judgment-form ML
;  #:mode (W I I O O)
;  #:contract (W Γ e S τ)
;  [
;   (where σ #{lookup A X})
;   --- var
;   (W A X () τ_sub)]

(define-metafunction ML
  lookup : A X -> σ
  [(lookup A X)
   σ
   (where ((X_0 σ_0) ... (X σ) (X_1 σ_1) ...) A)])

;; Definition 3.3 : occurrences of constructors
;;  let C be set of constructors, Σ(C,X) set of terms over C with variables X
;;  then occur(c,t) for c ∈ C and term t is:
;;  - 1                          if t = c(....)
;;  - occur(c,t1) + occur(c,t2)  if t = + t1 t2
;;  - 0                          else

;; Definition 3.4 : t ∈ Σ(C u {+}, X) is _discriminative_ iff occur(?,?) <= 1

;; ! = present, - = absent
;; sub/super types are just substitution instances
;; can use **Milner algorithm** to generate and solve constraints

;; Lemma 3.1 : leading constructors
;;  anything +(t1, t2) can be rewritten +(c(....), t3) 

;; =============================================================================
;; Chapter 4

;; Definition 4.16 : Algorithm W, referring to circular unification


