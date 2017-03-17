#lang racket

(provide
  reflexive-transitive-closure/deterministic)

(require
  redex/reduction-semantics)

;; =============================================================================

(define (reflexive-transitive-closure/deterministic --->)
  (define error-name (string->symbol (format "~a*" (object-name --->))))
  (lambda (t)
    (define v* (apply-reduction-relation* ---> t))
    (cond
     [(null? v*)
      (raise-user-error error-name "no result for ~a" t)]
     [(null? (cdr v*))
      (car v*)]
     [else
      (raise-user-error error-name "multiple results ~a --->* ~a" t v*)])))
