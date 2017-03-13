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
  [V ::= integer (λ x E)]
  [E e ::= V x (E E) (if0 E E E)]
  [V+ ::= (integer @ l) ((λ (x @ β) E+) @ l)]
  [E+ ::= V+ (x @ β) ((E+ E+) @ l) ((if0 E+ E+ E+) @ l) ((blame λ R) @ l) (E+ @ l)]
  [N ::= natural]
  [Γ ::= ((x β) ...)]
  [CTX ::= hole ((CTX E+) @ l) ((V+ CTX) @ l) ((if0 CTX E+ E+) @ l)]
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
   (annotate N Γ integer (integer @ l) N_1)]
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
  ref : Γ x -> β
  [(ref Γ x)
   β
   (where ((x_0 β_0) ... (x β) (x_1 β_1) ...) Γ)])

(module+ test
  (test-case "ref"
    (let ([Γ (term ((x β0) (y β1) (z β2)))])
      (check-true (Γ? Γ))
      (check-apply* (λ (t) (term #{ref ,Γ ,t}))
       [(term x)
        ==> (term β0)]
       [(term y)
        ==> (term β1)]
       [(term z)
        ==> (term β2)]))))

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
    [-->  (((integer @ l_0) V+) @ l_2)
          ((blame λ R) @ l_2)
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
      ==> (term ((blame λ R) @ l2))]
     [(term ((if0 (0 @ l0) (1 @ l1) (2 @ l2)) @ l3))
      ==> (term (1 @ l1))]
     [(term ((if0 (1 @ l0) (1 @ l1) (2 @ l2)) @ l3))
      ==> (term (2 @ l2))])
  ))
