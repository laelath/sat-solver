#lang racket

(require racket/fixnum)

(define (negate l)
  (fx* l -1))

(define (remove-var f l)
  (let ([¬l (negate l)])
    (list->set
     (map (λ (cl) (set-remove cl ¬l))
          (filter (λ (cl) (not (set-member? cl l)))
                  (set->list f))))))

(define (var-counts f)
  (define counts (make-hasheq))
  (set-for-each f (λ (cl) (set-for-each cl (λ (l) (dict-update! counts l add1 0)))))
  counts)

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
    [(set-empty? f) (sort σ fx< #:key fxabs)]
    [(set-member? f (seteq)) 'UNSAT]
    [else
     (let ([units (stream-filter (λ (cl) (= (set-count cl) 1)) (set->stream f))])
       (if (not (stream-empty? units))
           (let ([l (set-first (stream-first units))])
             (solve (remove-var f l) (cons l σ)))
           (let* ([counts (var-counts f)]
                  [pure? (find-pure counts)])
             (if pure?
                 (solve (remove-var f pure?) (cons pure? σ))
                 (let* ([l (car (argmax cdr (dict->list counts)))]
                        [σ1 (solve (remove-var f l) (cons l σ))])
                   (if (not (eq? σ1 'UNSAT))
                       σ1
                       (solve (remove-var f (negate l)) (cons (negate l) σ))))))))]))


(define (CNF P)
  
  (define counter 0)
  (define (next-var!)
    (begin (set! counter (fx+ counter 1))
           counter))

  (define vars (make-hasheq))

  (define (lookup-var p)
    (hash-ref! vars p next-var!))

  (define (trivial? P)
    (match P
      [n #:when (fixnum? n) #t]
      [p #:when (symbol? p) #t]
      [`(,P1 ∧ ,P2) #f]
      [`(,P1 ∨ ,P2) #f]
      [`(¬ ,P1) (trivial? P1)]))

  (define (simplify-trivial P)
    (match P
      [n #:when (fixnum? n) n]
      [p #:when (symbol? p) (lookup-var p)]
      [`(¬ ,P1)
       (match P1
         [n #:when (fixnum? n) (negate n)]
         [p #:when (symbol? p) (negate (lookup-var p))]
         [`(¬ ,P2) (simplify-trivial P2)])]))
  
  (define (conv P)
    (match P
      [n #:when (fixnum? n) (set (seteq n))]
      [p #:when (symbol? p) (set (seteq (lookup-var p)))]
      [`(,P1 ∧ ,P2) (set-union (conv P1) (conv P2))]
      [`(,P1 ∨ ,P2)
       (cond
         [(trivial? P1)
          (let ([l (simplify-trivial P1)])
            (list->set (set-map (conv P2) (λ (cl) (set-add cl l)))))]
         [(trivial? P2)
          (let ([l (simplify-trivial P2)])
            (list->set (set-map (conv P1) (λ (cl) (set-add cl l)))))]
         [else
          (let ([z (next-var!)])
            (conv `((,z ∨ ,P1) ∧ ((¬ ,z) ∨ ,P2))))])]
      [`(¬ ,P1)
       (match P1
         [n #:when (fixnum? n) (set (seteq (negate n)))]
         [p #:when (symbol? p) (set (seteq (negate (lookup-var p))))]
         [`(,P2 ∧ ,P3) (conv `((¬ ,P2) ∨ (¬ ,P3)))]
         [`(,P2 ∨ ,P3) (conv `((¬ ,P2) ∧ (¬ ,P3)))]
         [`(¬ ,P2) (conv P2)])]))

  (values (conv P) (dict->list vars) counter))

(define (expand-defs P)
  (match P
    ['ff `(ff ∧ (¬ ff))]
    ['tt `(tt ∨ (¬ tt))]
    [p #:when (symbol? p) p]
    [`(,P1 ,(or '∧ '^) ,P2) `(,(expand-defs P1) ∧ ,(expand-defs P2))]
    [`(,P1 ,(or '∨ 'v) ,P2) `(,(expand-defs P1) ∨ ,(expand-defs P2))]
    [`(,(or '¬ 'not '!) ,P1) `(¬ ,(expand-defs P1))]
    [`(,P1 ,(or '-> '=>) ,P2) `((¬ ,(expand-defs P1)) ∨ ,(expand-defs P2))]
    [`(,P1 ,(or '<-> '<=>) ,P2)
     (let ([Q1 (expand-defs P1)]
           [Q2 (expand-defs P2)])
       `(((¬ ,Q1) ∨ ,Q2) ∧ ((¬ ,Q2) ∨ ,Q1)))]
    [`(and ,P1) (expand-defs P1)]
    [`(and ,P1 ,P* ...) `(,(expand-defs P1) ∧ ,(expand-defs `(and ,@P*)))]
    [`(or ,P1) (expand-defs P1)]
    [`(or ,P1 ,P* ...) `(,(expand-defs P1) ∨ ,(expand-defs `(and ,@P*)))]))

(define (satisfiable? P)
  (let-values ([(f m _) (CNF (expand-defs P))])
    (let ([m (map (λ (p) (cons (cdr p) (car p))) m)])
      (match (solve f)
        ['UNSAT #f]
        [s (filter-map (λ (n)
                         (match (assoc (fxabs n) m)
                           [(or #f (cons _ (or 'tt 'ff))) #f]
                           [(cons _ p) (cons p (positive? n))]))
                       s)]))))

(define (tautology? P)
  (match (satisfiable? `(¬ ,P))
    [#f #t]
    [s s]))

(define (string->fixnum s)
  (let ([n (string->number s)])
    (unless (fixnum? n)
      (error (format "number not a fixnum: ~a" s)))
    n))

(define (parse s)
  (let* ([lines (filter (λ (l) (not (or (string-prefix? l "c") (string-prefix? l "p"))))
                        (string-split s "\n"))])
    (list->set
     (map (λ (cl)
            (list->seteq
             (map string->fixnum
                  (string-split (substring cl 0 (- (string-length cl) 2))))))
          lines))))

(define (solve-file p)
  (solve (parse (file->string p))))






















