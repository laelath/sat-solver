#lang racket

(define (negate l)
  (match l
    [`(¬ ,p) p]
    [p `(¬ ,p)]))

(define (lit-var l)
  (match l
    [`(¬ ,p) p]
    [p p]))

(define (remove-var f l)
  (let ([¬l (negate l)])
    (list->set
     (map (λ (cl) (set-remove cl ¬l))
          (filter (λ (cl) (not (set-member? cl l)))
                  (set->list f))))))

(define (var-counts fstream)
  (stream-fold
   (λ (counts cl)
     (stream-fold
      (λ (counts l) (dict-update counts l add1 0))
      counts (set->stream cl)))
   #hash() fstream))

(define (find-pure counts)
  (let loop ([pos (dict-iterate-first counts)])
    (let ([l (dict-iterate-key counts pos)]
          [npos? (dict-iterate-next counts pos)])
      (cond
        [(not (dict-has-key? counts (negate l))) l]
        [npos? (loop npos?)]
        [else #f]))))
          

(define (solve f [σ '()])
  (cond
    [(set-empty? f) σ]
    [(set-member? f (set)) 'UNSAT]
    [else
     (let* ([fstream (set->stream f)]
            [units (stream-filter (λ (cl) (= (set-count cl) 1)) fstream)])
       (if (not (stream-empty? units))
           (let ([l (set-first (stream-first units))])
             (solve (remove-var f l) (cons l σ)))
           (let* ([counts (var-counts fstream)]
                  [pure? (find-pure counts)])
             (if pure?
                 (solve (remove-var f pure?) (cons pure? σ))
                 (let* ([l (car (argmax cdr (dict->list counts)))]
                        [σ1 (solve (remove-var f l) (cons l σ))])
                   (if (not (equal? σ1 'UNSAT))
                       σ1
                       (solve (remove-var f (negate l)) (cons (negate l) σ))))))))]))

(define (trivial? P)
  (match P
    [p #:when (symbol? p) #t]
    [`(,P1 ∧ ,P2) #f]
    [`(,P1 ∨ ,P2) #f]
    [`(¬ ,P1) (trivial? P1)]))

(define (simplify-trivial P)
  (match P
    [p #:when (symbol? p) p]
    [`(¬ ,P1)
     (match P1
       [p #:when (symbol? p) P]
       [`(¬ ,P2) (simplify-trivial P2)])]))

(define (CNF P)
  (match P
    [p #:when (symbol? p) (set (set p))]
    [`(,P1 ∧ ,P2) (set-union (CNF P1) (CNF P2))]
    [`(,P1 ∨ ,P2)
     (cond
       [(trivial? P1)
        (let ([l (simplify-trivial P1)])
          (list->set (set-map (CNF P2) (λ (cl) (set-add cl l)))))]
       [(trivial? P2)
        (let ([l (simplify-trivial P2)])
          (list->set (set-map (CNF P1) (λ (cl) (set-add cl l)))))]
       [else
        (let ([z (gensym)])
          (CNF `((,z ∨ ,P1) ∧ ((¬ ,z) ∨ ,P2))))])]
    [`(¬ ,P1)
     (match P1
       [p #:when (symbol? p) (set (set `(¬ ,p)))]
       [`(,P2 ∧ ,P3) (CNF `((¬ ,P2) ∨ (¬ ,P3)))]
       [`(,P2 ∨ ,P3) (CNF `((¬ ,P2) ∧ (¬ ,P3)))]
       [`(¬ ,P2) (CNF P2)])]))

(define (expand-defs P)
  (match P
    [p #:when (symbol? p) p]
    [(or `(,P1 ∧ ,P2) `(,P1 ^ ,P2)) `(,(expand-defs P1) ∧ ,(expand-defs P2))]
    [(or `(,P1 ∨ ,P2) `(,P1 v ,P2)) `(,(expand-defs P1) ∨ ,(expand-defs P2))]
    [(or `(¬ ,P1) `(not ,P1) `(! ,P1)) `(¬ ,(expand-defs P1))]
    [`(,P1 -> ,P2) `((¬ ,(expand-defs P1)) ∨ ,(expand-defs P2))]
    [`(,P1 <-> ,P2)
     (let ([Q1 (expand-defs P1)]
           [Q2 (expand-defs P2)])
       `(((¬ ,Q1) ∨ ,Q2) ∧ ((¬ ,Q2) ∨ ,Q1)))]
    [`(and ,P1) (expand-defs P1)]
    [`(and ,P1 ,P* ...) `(,(expand-defs P1) ∧ ,(expand-defs `(and ,@P*)))]
    [`(or ,P1) (expand-defs P1)]
    [`(or ,P1 ,P* ...) `(,(expand-defs P1) ∨ ,(expand-defs `(and ,@P*)))]))

(define (tautology? P)
  (solve (CNF `(¬ ,(expand-defs P)))))

(define (parse s)
  (let* ([lines (filter (λ (l) (not (or (string-prefix? l "c") (string-prefix? l "p"))))
                        (string-split s "\n"))])
    (list->set
     (map (λ (cl)
            (list->set
             (map (λ (l)
                    (if (string-prefix? l "-")
                        `(¬ ,(string->symbol (string-append "x" (substring l 1))))
                        (string->symbol (string-append "x" l))))
                  (string-split (substring cl 0 (- (string-length cl) 2))))))
          lines))))

(define (solve-file p)
  (solve (parse (file->string p))))






















