#lang racket
(require redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language bool-any-lang
  [B true false (V B B)]
  [C (V C B) (V B C) hole])

(define B1 (term true))
(define B2 (term false))
(define B3 (term (V true false)))
(define B4 (term (V ,B1 ,B2)))
(define B5 (term (V false ,B4)))

(define C1 (term hole))
(define C2 (term (V (V false false) hole)))
(define C3 (term (V hole true)))

(module+ test
  (check-true
    (redex-match? bool-any-lang B (term (V false true))))
  (check-true
    (redex-match? bool-any-lang (in-hole C (V true B)) (term (V true (V true false)))))
)

(define bool-any-red
  (reduction-relation
    bool-any-lang
    (--> (in-hole C (V true B))
         (in-hole C true)
         V-true)
    (--> (in-hole C (V false B))
         (in-hole C B)
         V-false)))

(module+ test
  (check-true
    (redex-match? bool-any-lang
      (in-hole C (V true B))
      (term (V (V true (V false true)) false))))

  #;(traces bool-any-red (term (V (V true false) (V true true))))
)

(define-language bool-standard-lang
  [B true false (V B B)]
  [E (V E B) hole])

(define bool-standard-red
  (reduction-relation
    bool-standard-lang
    (--> (in-hole E (V true B))
         (in-hole E true)
         V-true)
    (--> (in-hole E (V false B))
         (in-hole E B)
         V-false)))

(module+ test
  (let ([T0 (term (V (V true false) (V true true)))]
        [T1 (term (V true (V true true)))]
        [T2 (term true)])
    (test--> bool-standard-red T0 T1)
    (test--> bool-standard-red T1 T2)))

;; =============================================================================

(module+ test
  (test-results))
