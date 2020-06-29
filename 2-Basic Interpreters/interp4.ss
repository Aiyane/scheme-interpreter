(load "record.ss")

;; 接收 env 参数，传入全局表，解释函数时将参数添加到 env 中构成新 env

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
       (λ (e env)
         (variant-case e
           [lit (datum) datum]
           [varref (var) (apply-env env var)]
           [app (rator rands)
             ((eval-exp rator env)
              (map (λ (x) (eval-exp x env))
                rands))]
           [lambda (formals body)
             (λ (args)
               (eval-exp body
                 (λ (sym)
                   (if (memq sym formals)
                       (little-lookup sym formals args)
                       (apply-env env sym)))))]))]
     [apply-env
       (λ (env sym) (env sym))]
     [little-lookup
       (λ (item item-list match-list)
         (list-ref match-list
           (find-lexical-address-ONE item item-list)))]
     [find-lexical-address-ONE
       (λ (e cenv)
         (letrec
           ([find-lexical-address
              (λ (cenv)
                (cond
                  [(eq? (car cenv) e) 0]
                  [else (add1 (find-lexical-address (cdr cenv)))]))])
           (find-lexical-address cenv)))]
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
    (λ (e env)
      (eval-exp (parse-exp e) env))))

#|
> (eval-exp '(((lambda (x y)
                 (lambda (z k)
                   (+ x (+ y (* z k))))) 
                1 2) 3 4)
    global-table)
15
|#
