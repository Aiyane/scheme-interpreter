(load "record.ss")

;; 接收 table 参数，传入全局表，还是不支持函数

;; 数字
(define-record lit (datum))
(define-record varref (var))
(define-record lambda (formals body))
(define-record app (rator rands))


(define global-table
  (let ([apply* (λ (args)
                  (* (car args) (cadr args)))]
        [apply+ (λ (args)
                  (+ (car args) (cadr args)))]
        [apply-cons (λ (args)
                      (cons (car args) (cadr args)))]
        [apply-car (λ (args)
                     (car (car args)))]
        [apply-cdr (λ (args)
                     (cdr (car args)))])
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

(define eval-exp
  (letrec
    ([eval-exp
       (λ (e table)
         (variant-case e
           [lit (datum) datum]
           [varref (var) (table var)]
           [app (rator rands)
             ((eval-exp rator table)
              (map (λ (x) (eval-exp x table))
                rands))]))]
     [parse-exp
       (λ (e)
         (cond
           [(number? e) (make-lit e)]
           [(atom? e) (make-varref e)]
           [(and (list? e)
                 (eq? (car e) 'lambda))
            (make-lambda (cadr e)
              (parse-exp (caddr e)))]
           [else
             (make-app (parse-exp (car e))
               (map parse-exp (cdr e)))]))])
    (λ (e table)
      (eval-exp (parse-exp e) table))))
