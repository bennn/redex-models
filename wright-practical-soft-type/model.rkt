#lang mf-apply racket/base

(require
  "../utils.rkt"
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit rackunit-abbrevs))

;; =============================================================================

(define-language Λ
  [e ::= v (e e)]
  [v ::= c x (λ (x) e)]
  [c ::= ;; Const
         basic-constants
         primitive-operations]
  [a ::= ;; answers
         v CHECK]
  [E ::= ;; evaluation context
         hole (E e) (v E)]
  [basic-constants ::= integer TRUE FALSE]
  [primitive-operations ::= + - * / add1 not]
  [x* ::= (x ...)]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
    (λ (x) e #:refers-to x))
;; all functions curried, including + etc.

(define e? (redex-match? Λ e))
(define v? (redex-match? Λ v))
(define c? (redex-match? Λ c))

(module+ test
  (test-case "rwdex-match"
    (check-pred e? (term (not TRUE)))

    (check-pred c? (term not))
    (check-pred c? (term 42))

    (check-pred v? (term TRUE))))

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
  δ : c v -> a
  [(δ not TRUE)
   FALSE]
  [(δ not FALSE)
   TRUE]
  [(δ not v)
   CHECK]
  [(δ add1 integer)
   ,(+ 1 (term integer))]
  [(δ c v)
   ,(raise-user-error 'δ "undefined for ~a ~a" (term c) (term v))])

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
      (term 6))))

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
        δ_2]))

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
      ==> (term 2)])
  )
)


