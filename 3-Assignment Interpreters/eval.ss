(load "record.ss")

;; 由 interp8.ss 文件变换而来
;; 移除了 primitive 操作中的高阶函数。增加 if 条件语句

(define-record lit (datum))                     ; 数字
(define-record varref (var))                    ; 变量
(define-record lambda (formals body))           ; 函数
(define-record app (rator rands))               ; 调用
(define-record if (test-exp then-exp else-exp)) ; if
(define-record extended-env (formals args env)) ; 环境
(define-record closure (formals body env))      ; 闭包
(define-record primitive (sym))                 ; 原语

(define find-lexical-address-ONE
  (λ (e cenv)
    (letrec ([find-lexical-address
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
  (λ (env sym)
    (variant-case env
      [extended-env (formals args env)
        (if (memq sym formals)
            (little-lookup sym formals args)
            (apply-env env sym))]
      [else (global-table sym)])))

; 调用语句既可以是闭包，也可以是原语操作
(define apply-closure
  (λ (closure args)
    (variant-case closure
      [closure (formals body env)
        (eval-exp body
          (make-extended-env
            formals args env))]
      [primitive (sym)
        (apply-primitive sym args)])))

; 使用了 eval 内置的解释器运行
(define apply-primitive
  (λ (sym args)
    (case sym
      [(zero?)
       (let ([x (apply (eval sym) args)])
         (if x 1 0))]
      [else
        (apply (eval sym) args)])))

(define global-table
  (let ([apply* (make-primitive '*)]
        [apply+ (make-primitive '+)]
        [apply-cons (make-primitive 'cons)]
        [apply-car (make-primitive 'car)]
        [apply-cdr (make-primitive 'cdr)]
        [apply-zero? (make-primitive 'zero?)])
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
        [(true) 1]
        [(false) 0]
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
             (apply-closure (eval-exp rator env)
               (map (λ (x) (eval-exp x env))
                 rands))]
           [lambda (formals body)
             (make-closure formals body env)]
           [if (test-exp then-exp else-exp)
             (cond
               [(zero? (eval-exp test-exp env))
                 (eval-exp else-exp env)]
               [else (eval-exp then-exp env)])]))])
    (λ (e env)
      (eval-exp e env))))

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
      (eval-exp (parse-exp unparsed-expression) global-table))))
