#lang racket
(require redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language modulo-3-lang
  [A 0 1 2 (A + A)]
  [C hole (C + A) (A + C)])

(define A1 (term 0))
(define A2 (term 2))
(define A3 (term (0 + 1)))
(define A4 (term (,A3 + ,A3)))
(define A5 (term (2 + ,A4)))

(define C1 (term hole))
(define C2 (term (hole + ,A3)))
(define C3 (term (2 + (2 + hole))))

(module+ test
  (for ([a (in-list (list A1 A2 A3 A4 A5))])
    (check-true (redex-match? modulo-3-lang A a)))
  (check-true
    (redex-match? modulo-3-lang (in-hole C (2 + 2)) (term (0 + (1 + (2 + 2))))))
)

(define modulo-3-red
  (reduction-relation
    modulo-3-lang
    (--> (in-hole C (0 + A))
         (in-hole C A)
         +0-L)
    (--> (in-hole C (A + 0))
         (in-hole C A)
         +0-R)
    (--> (in-hole C (natural_0 + natural_1))
         (in-hole C ,(modulo (+ (term natural_0) (term natural_1)) 3))
         +N)))

(module+ test
  (test-->> modulo-3-red A2 (term 2))
  (test-->> modulo-3-red A3 (term 1))
  (test-->> modulo-3-red A4 (term 2))
  (test-->> modulo-3-red A5 (term 1)))

(define-language mod3-standard
  [N 0 1 2]
  [A N (A + A)]
  [C hole (C + A) (N + C)])

(define mod3-standard-red
  (reduction-relation
    mod3-standard
    (--> (in-hole C (natural_0 + natural_1))
         (in-hole C ,(modulo (+ (term natural_0) (term natural_1)) 3))
         +N)))

(module+ test
  (test-->> mod3-standard-red A2 (term 2))
  (test-->> mod3-standard-red A3 (term 1))
  (test-->> mod3-standard-red A4 (term 2))
  (test-->> mod3-standard-red A5 (term 1))

  (check-equal?
    (length (apply-reduction-relation mod3-standard-red A5))
    1)
)

;; =============================================================================

(module+ test
  (test-results))
