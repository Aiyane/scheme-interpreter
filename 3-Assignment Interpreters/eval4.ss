(load "record.ss")

;; 增加空环境
#|
> (run
    '((lambda (n)
        ((lambda (!)
           (! n !))
         (lambda (n bang)
           (if (zero? n)
               1
               (* n (bang (- n 1) bang))))))
      8))
40320
> (run '(set! true 100))
> (run '((lambda (x) true)
         (set! true 998)))
998
> (run '((lambda (x) zero?)
         (set! true 998)))
#(primitive zero?)
> (run '((lambda (x) zero?)
         (set! zero? 1239)))
1239
> (run '((lambda (x) zero?)
         (set! zero? *)))
#(primitive *)
> (run '((lambda (x) (zero? 3 4))
         (set! zero? *)))
12
|#


(define-record lit (datum))                     ; 数字
(define-record varref (var))                    ; 变量
(define-record lambda (formals body))           ; 函数
(define-record app (rator rands))               ; 调用
(define-record if (test-exp then-exp else-exp)) ; if
(define-record varassign (var exp))             ; 赋值
(define-record extended-env (formals args env)) ; 环境
(define-record closure (formals body env))      ; 闭包
(define-record primitive (sym))                 ; 原语
(define-record empty-env ())                    ; 空环境

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
      [empty-env ()
        (global-table sym)]
      [else (error 'apply-env "Something bad happened.")])))

; 调用语句既可以是闭包，也可以是原语操作
(define apply-closure
  (λ (closure args)
    (variant-case closure
      [closure (formals body env)
        (eval-exp body
          (make-extended-env
            formals (map box args) env))]
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
  (let ([apply* (box (make-primitive '*))]
        [apply+ (box (make-primitive '+))]
        [apply- (box (make-primitive '-))]
        [apply-cons (box (make-primitive 'cons))]
        [apply-car (box (make-primitive 'car))]
        [apply-cdr (box (make-primitive 'cdr))]
        [apply-zero? (box (make-primitive 'zero?))]
        [boxed1 (box 1)]
        [boxed0 (box 0)])
    (λ (sym)
      (case sym
        [(cons) apply-cons]
        [(car) apply-car]
        [(cdr) apply-cdr]
        [(zero?) apply-zero?]
        [(*) apply*]
        [(+) apply+]
        [(-) apply-]
        [(true) boxed1]
        [(false) boxed0]
        [else
          (errorf 'global-table "unbound variable: ~s" sym)]))))

(define eval-exp
  (letrec 
    ([eval-exp
       (λ (e env)
         (variant-case e
           [lit (datum) datum]
           [varref (var) (unbox (apply-env env var))]
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
               [else (eval-exp then-exp env)])]
           [varassign (var exp)
             (set-box!
               (apply-env env var)
               (eval-exp exp env))]))])
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
                 (eq? (car e) 'set!))
            (make-varassign (cadr e)
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
      (eval-exp (parse-exp unparsed-expression) (make-empty-env)))))
