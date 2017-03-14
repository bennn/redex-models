#lang mf-apply racket/base

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (printf "[DEBUG] ")
    (apply printf msg arg*)
    (newline)))

;; =============================================================================
;; Chapter 3: The Lambda Calculus

(define-language Λ
  [n ::= integer]
  [V ::= n (λ x E)]
  [E e ::= V x (E E) (if0 E E E)]
  [V+ ::= (n @ l) ((λ (x @ β) E+) @ l)]
  [E+ ::= V+ (x @ β) ((E+ E+) @ l) ((if0 E+ E+ E+) @ l) ((blame l SEV) @ l) (E+ @ l)]
  [N ::= natural]
  [Γ ::= ((x β) ...)]
  [CTX ::= hole ((CTX E+) @ l) ((V+ CTX) @ l) ((if0 CTX E+ E+) @ l)]
  [SEV ::= ;; severity
           R O]
  [φ ::= ((l (l ...)) ...)]
  [ψ ::= ((l (l SEV)) ...)]
  [PP ::= (φ ψ)]
  [l β x ::= variable-not-otherwise-mentioned]
  #:binding-forms
    (λ x E #:refers-to x)
    ((λ (x @ β) E+ #:refers-to x) @ l))

(define V? (redex-match? Λ V))
(define E? (redex-match? Λ E))
(define e? (redex-match? Λ e))
(define V+? (redex-match? Λ V+))
(define E+? (redex-match? Λ E+))
(define Γ? (redex-match? Λ Γ))
(define N? (redex-match? Λ N))

(define (Λ=? t0 t1)
  (alpha-equivalent? Λ t0 t1))

(module+ test
  (test-case "redex-match:basic"
    (check-pred Γ? (term ()))
    (check-pred Γ? (term ((x β))))
    (check-pred Γ? (term ((x β0))))

    (check-pred E? (term 3))
    (check-pred E? (term (λ x x)))
    (check-pred E? (term ((λ x x) 3)))
    (check-pred e? (term ((λ x x) 3)))

    (check-pred V+? (term (3 @ l)))
    (check-pred E+? (term (3 @ β0)))
    (check-pred E+? (term (x @ β0)))
    (check-pred V+? (term ((λ (x @ β0) (x @ β0)) @ l1)))
    (check-pred E+? (term ((λ (x @ β0) (x @ β0)) @ l1)))
    (check-pred E+? (term (3 @ l3)))
    (check-pred E+? (term ((((λ (x«2» @ β0) (x«2» @ β0)) @ l1) (3 @ l3)) @ l4)))

    (check-pred N? (term 0))))

(define (fresh sym n)
  (list (string->symbol (format "~a~a" sym n)) (+ n 1)))

(define (fresh-term n)
  (fresh 'l n))

(define (fresh-var n)
  (fresh 'β n))

(module+ test
  (check-apply* fresh
   ['a 1
    ==> '(a1 2)]
   ['β 3
    ==> '(β3 4)]
   ['l 7
    ==> '(l7 8)]))

(define-judgment-form Λ
  #:mode (annotate I I I O O)
  #:contract (annotate N Γ E E+ N)
  [
   (side-condition ,(debug "INT"))
   (where (l N_1) ,(fresh-term (term N)))
   --- Int
   (annotate N Γ n (n @ l) N_1)]
  [
   (side-condition ,(debug "Lam"))
   (where (β_1 N_1) ,(fresh-var (term N_0)))
   (where Γ_1 ,(cons (term (x β_1)) (term Γ_0)))
   (annotate N_1 Γ_1 E E+_2 N_2)
   (where (l_2 N_3) ,(fresh-term (term N_2)))
   (where E+ ((λ (x @ β_1) E+_2) @ l_2))
   --- Lam
   (annotate N_0 Γ_0 (λ x E) E+ N_3)]
  [
   (side-condition ,(debug "var"))
   (where β #{ref Γ_0 x})
   --- Var
   (annotate N_0 Γ_0 x (x @ β) N_0)]
  [
   (side-condition ,(debug "app"))
   (annotate N_0 Γ_0 e_0 E+_0 N_1)
   (annotate N_1 Γ_0 e_1 E+_1 N_2)
   (where (l_2 N_3) ,(fresh-term (term N_2)))
   (where E+_2 ((E+_0 E+_1) @ l_2))
   --- App
   (annotate N_0 Γ_0 (e_0 e_1) E+_2 N_3)]
  [
   (side-condition ,(debug "if0"))
   (annotate N_0 Γ_0 e_0 E+_0 N_1)
   (annotate N_1 Γ_0 e_1 E+_1 N_2)
   (annotate N_2 Γ_0 e_2 E+_2 N_3)
   (where (l_3 N_4) ,(fresh-term (term N_3)))
   (where E+_3 ((if0 E+_0 E+_1 E+_2) @ l_3))
   --- If0
   (annotate N_0 Γ_0 (if0 e_0 e_1 e_2) E+_3 N_4)])

(define-metafunction Λ
  ref : any x -> any
  [(ref Γ x)
   β
   (where ((x_0 β_0) ... (x β) (x_1 β_1) ...) Γ)]
  [(ref φ x)
   (l ...)
   (where ((x_0 (l_0 ...)) ... (x (l ...)) (x_1 (l_1 ...)) ...) φ)]
  [(ref ψ x)
   (l SEV)
   (where ((x_0 (l_0 SEV_0)) ... (x (l SEV)) (x_1 (l_1 SEV_1)) ...) Γ)])

(define-metafunction Λ
  update : any x any -> any
  [(update any_0 x any_1)
   ((x_2 any_2) ... (x any_1) (x_3 any_3) ...)
   (where ((x_2 any_2) ... (x any_4) (x_3 any_3) ...) any_0)]
  [(update any_0 x any_1)
   ((x any_1) (x_2 any_2) ...)
   (where ((x_2 any_2) ...) any_0)])

(module+ test
  (let ([Γ (term ((x β0) (y β1) (z β2)))])
    (test-case "redex-match:env"
      (check-true (Γ? Γ)))
    (test-case "ref"
      (check-apply* (λ (t) (term #{ref ,Γ ,t}))
       [(term x)
        ==> (term β0)]
       [(term y)
        ==> (term β1)]
       [(term z)
        ==> (term β2)]))
    (test-case "update"
      (check-apply* (λ (t u) (term #{update ,Γ ,t ,u}))
       [(term x) (term β3)
        ==> (term ((x β3) (y β1) (z β2)))]
       [(term y) (term β3)
        ==> (term ((x β0) (y β3) (z β2)))]))
))

(define-metafunction Λ
  [(annotate# E)
   E+
   (judgment-holds (annotate 0 () E E+ N))]
  [(annotate# E)
   ,(raise-user-error 'annotate "undefined for ~a" (term E))])

(module+ test
  (test-case "annotate:basic"
    (check Λ=?
      ;; TODO could do α-equivalence, but need to bind the labels.
      ;;  so like, get free variables then make a ∀ term?
      (term #{annotate# 3})
      (term (3 @ l0))))

  (test-case "annotate:example"
    (let ([t (term ((λ x x) 3))])
      (check-pred E? t)
      (let ([t1 (term #{annotate# ,t})])
        (check-pred E+? t1)
        (check Λ=? t1 (term ((((λ (x @ β0) (x @ β0)) @ l1) (3 @ l2)) @ l3)))
        (void)))))

(define --->
  (reduction-relation Λ
    #:domain E+
    [--> ((((λ (x @ β) E+) @ l_0) V+) @ l_2)
         (substitute E+ x V+)
         Subst]
    [-->  (((n @ l_0) V+) @ l_2)
          ((blame TOP R) @ l_2)
          App-Error]
    [--> ((if0 (0 @ l_0) E+_1 E+_2) @ l_3)
         E+_1
         If-True]
    [--> ((if0 V+ E+_1 E+_2) @ l_3)
         E+_2
         (side-condition (not (zero? (car (term V+)))))
         If-False]
    [--> (V+ @ β_0)
         V+
         ;; because our substitution isn't exactly like meunier's
         Var]))

(define (--->* t)
  (define v* (apply-reduction-relation* ---> t))
  (cond
   [(null? v*)
    (raise-user-error '--->* "no result for ~a" t)]
   [(null? (cdr v*))
    (car v*)]
   [else
    (raise-user-error '--->* "multiple results ~a --->* ~a" t v*)]))

(module+ test
  (test-case "--->*:based"
    (check-pred V+? (term ((λ (x @ β0) (x @ β0)) @ l0)))
    (check-pred V+? (term (4 @ l1)))
    (check-pred E+? (term ((((λ (x @ β0) (x @ β0)) @ l0) (4 @ l1)) @ l2)))
    (check-apply* --->*
     [(term (0 @ l0))
      ==> (term (0 @ l0))]
     [(term ((((λ (x @ β0) (x @ β0)) @ l0) (4 @ l1)) @ l2))
      ==> (term (4 @ l1))]
     [(term (((2 @ l0) (2 @ l1)) @ l2))
      ==> (term ((blame TOP R) @ l2))]
     [(term ((if0 (0 @ l0) (1 @ l1) (2 @ l2)) @ l3))
      ==> (term (1 @ l1))]
     [(term ((if0 (1 @ l0) (1 @ l1) (2 @ l2)) @ l3))
      ==> (term (2 @ l2))])
  ))

(define-judgment-form Λ
  #:mode (init-constraints I I O)
  #:contract (init-constraints (φ ψ) E+ (φ ψ))
  [
   (where φ_1 #{⊆ {l} (φ l)})
   --- Init-Int
   (init-constraints (φ ψ) (n @ l) (φ_1 ψ))]
  [
   (where φ_1 #{⊆ {l} (φ l)})
   (init-constraints (φ_1 ψ) E+ (φ_2 ψ_2))
   --- Init-λ
   (init-constraints (φ ψ) ((λ (x β) E+) @ l) (φ_2 ψ_2))]
  [
   --- Init-Var
   (init-constraints (φ ψ) (x @ l) (φ ψ))]
  [
   (init-constraints (φ ψ) E+_0 (φ_0 ψ_0))
   (init-constraints (φ_0 ψ_0) E+_1 (φ_1 ψ_1))
   --- Init-App
   (init-constraints (φ ψ) (E+_0 E+_1) (φ_1 ψ_1))]
  [
   (init-constraints (φ ψ) E+_0 (φ_0 ψ_0))
   (init-constraints (φ_0 ψ_0) E+_1 (φ_1 ψ_1))
   (init-constraints (φ_1 ψ_1) E+_2 (φ_2 ψ_2))
   (where (any_1 @ l_1) E+_1)
   (where (any_2 @ l_2) E+_2)
   (where φ_3 #{⊆ #{ref φ_2 l_1} (φ_2 l)})
   (where φ_4 #{⊆ #{ref φ_3 l_2} (φ_3 l)})
   --- Init-If
   (init-constraints (φ ψ) ((if0 E+_0 E+_1 E+_2) @ l) (φ_4 ψ_2))]
  [
   (where ψ_1 #{⊆ ((λ R)) (ψ l)})
   --- Init-Blame
   (init-constraints (φ ψ) ((blame TOP R) @ l) (φ ψ_1))])

(define-metafunction Λ
  ⊆ : any any -> any
  [(⊆ (l_0 ...) (φ l_1))
   #{update φ l_1 ,(set-union (term (l_0 ...)) (term (l_2 ...)))}
   (where (l_2 ...) #{ref φ l_1})]
  [(⊆ ((l_0 SEV_0) ...) (ψ l_1))
   #{update ψ l_1 ,(set-union (term ((l_0 SEV_0) ...)) (term ((l_2 SEV_2) ...)))}
   (where ((l_2 SEV_2) ...) #{ref ψ l_1})])

;;; ENV ⊢ source sink ⊣ ENV
;(define-judgment-form Λ
;  #:mode (simple-constraint-creation I I I O)
;  #:contract (simple-constraint-creation (φ ψ) E+ E+ (φ ψ))
;  [
;   ;; if l_0 in l_5 add error to ψ l_7
;   (where PP TODO)
;   --- IntApp
;   (simple-constraint-creation (φ_0 ψ_0) (n @ l_0) (((e_0 @ l_5) (e_1 @ l_6)) @ l_7) PP)]
;  [
;   --- LamApp
;
