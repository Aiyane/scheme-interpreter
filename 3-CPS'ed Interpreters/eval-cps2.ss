(load "record.ss")

;; 增加 apply-k

;; 数字
(define-record lit (datum))
(define-record varref (var))
(define-record lambda (formals body))
(define-record app (rator rands))
(define-record if (test-exp then-exp else-exp))

(define-record extended-env (formals args env))

; (define-record closure (formals body env))

(define apply-k
  (λ (k val)
    (k val)))

(define find-lexical-address-ONE
  (λ (e cenv)
    (letrec
      ([find-lexical-address
        (λ (cenv)
          (cond
            [(eq? (car cenv) e) 0]
            [else (add1 (find-lexical-address (cdr cenv)))]))])
      (find-lexical-address cenv))))


(define little-lookup
  (λ (item item-list match-list)
    (list-ref match-list
      (find-lexical-address-ONE item item-list))))


(define apply-env
  (λ (env sym k)
    (variant-case env
      [extended-env (formals args env)
        (if (memq sym formals)
            (apply-k k (little-lookup sym formals args))
            (apply-env env sym k))]
      [else (apply-k k (global-table sym))])))


; (define apply-closure
;   (λ (closure args)
;     (variant-case closure
;       [closure (formals body env)
;         (eval-exp body
;           (make-extended-env formals args env))]
;       [else (closure args)])))


(define global-table
  (let ([apply* (λ (args k)
                  (apply-k k (* (car args) (cadr args))))]
        [apply+ (λ (args k)
                  (apply-k k (+ (car args) (cadr args))))]
        [apply- (λ (arg k)
                  (apply-k k (- (car args) (cadr args))))]
        [apply-zero? (λ (args k)
                       (apply-k k (if (zero? (car args))
                              1 0)))]
        [apply-cons (λ (args k)
                      (apply-k k (cons (car args) (cadr args))))]
        [apply-car (λ (args k)
                     (apply-k k (car (car args))))]
        [apply-cdr (λ (args k)
                     (apply-k k (cdr (car args))))])
    (λ (sym)
      (case sym
        [(cons) apply-cons]
        [(car) apply-car]
        [(cdr) apply-cdr]
        [(X) 10]
        [(V) 5]
        [(D) 500]
        [(C) 100]
        [(I) 1]
        [(M) 1000]
        [(*) apply*]
        [(+) apply+]
        [else
          (errorf 'global-table "unbound variable: ~s" sym)]))))

(define eval-rands
  (λ (rands env k)
    (cond
      [(null? rands) (apply-k k '())]
      [else (eval-exp (car rands) env
              (λ (arg)
                (eval-rands (cdr rands) env
                  (λ (args)
                    (apply-k k (cons arg args))))))])))

(define eval-exp
  (letrec
    ([eval-exp
       (λ (e env k)
         (variant-case e
           [lit (datum) (apply-k k datum)]
           [varref (var) (apply-env env var k)]
           [if (test-exp then-exp else-exp)
             (eval-exp test-exp env
               (λ (b)
                 (if (zero? b)
                     (eval-exp else-exp env k)
                     (eval-exp then-exp env k))))]
           [app (rator rands)
             (eval-exp rator env
               (λ (proc)
                 (eval-rands rands env
                   (λ (args)
                     (proc args k)))))]
           [lambda (formals body)
             (apply-k k (λ (args k)
                  (eval-exp
                    body
                    (make-extended-env formals args env)
                    k)))]))])
    (λ (e env k)
      (eval-exp e env k))))


(define run
  (letrec
    ([parse-exp
       (λ (e)
         (cond
           [(number? e) (make-lit e)]
           [(atom? e) (make-varref e)]
           [(and (list? e)
                 (eq? (car e) 'lambda))
           (make-lambda (cadr e)
             (parse-exp (caddr e)))]
           [(and (list? e)
                 (eq? (car e) 'if))
            (make-if
              (parse-exp (cadr e))
              (parse-exp (caddr e))
              (parse-exp (cadddr e)))]
           [else
             (make-app (parse-exp (car e))
               (map parse-exp (cdr e)))]))])
    (λ (unparsed-expression)
      (eval-exp (parse-exp unparsed-expression)
        global-table
        (λ (x) x))))) ;; 增加 empty-k 参数

#|
> (run '(((lambda (x y)
            (lambda (z k)
              (+ x (+ y (* z k)))))
           1 2) 3 4))
15
|#
