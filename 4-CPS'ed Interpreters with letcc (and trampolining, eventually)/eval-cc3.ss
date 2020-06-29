(load "record.ss")

;; 将 k 参数改成全局参数，使之为寄存器形式

(define k* 'nobinding)

(define *k-trace* #f)

(define k-trace
  (λ ()
    (for-each display
      '("Kontinuation tracing enabled." #\newline))
    (set! *k-trace* #t)))

(define stop-k-trace
  (λ ()
    (for-each display
      '("Kontinuation tracing disabled." #\newline))
    (set! *k-trace* #f)))

(define show-k-trace
  (λ (k)
    (if *k-trace*
        (begin
          (display (vector-ref k 0))
          (newline)))))

;; 数字
(define-record lit (datum))
(define-record varref (var))
(define-record lambda (formals body))
(define-record app (rator rands))
(define-record if (test-exp then-exp else-exp))
(define-record letcc (var exp))

(define-record extended-env (formals args env))
(define-record closure (formals body env))
(define-record continuation-closure (kont))
(define-record primitive (sym))


;; This is used to add a single var (and a single arg) to the env. 
(define make-extended-env/1
  (λ (var arg env)
    (make-extended-env (list var) (list arg) env)))


(define-record post-test-k (then-exp else-exp env k))
(define-record post-rator-k (rands env k))
(define-record post-rands-k (proc k))
(define-record post-rest-rands-k (a k))
(define-record post-first-rands-k (rands env k))
(define-record final-k (jumpout))

(define apply-k
  (λ (arg)
    (cons k* arg)))

(define apply-k*
  (λ (val)
    (show-k-trace k*)
    (variant-case k*
      [final-k (jumpout) (jumpout val)]
      [post-test-k (then-exp else-exp env k)
        (if (zero? val)
            (begin
              (set! k* k)
              (eval-exp else-exp env))
            (begin
              (set! k* k)
              (eval-exp then-exp env)))]
      [post-rator-k (rands env k)
        (set! k* (make-post-rands-k val k))
        (eval-rands rands env)]
      [post-rands-k (proc k)
        (set! k* k)
        (apply-closure proc val)]
      [post-rest-rands-k (a k)
        (set! k* k)
        (apply-k (cons a val))]
      [post-first-rands-k (rands env k)
        (set! k* (make-post-rest-rands-k val k))
        (eval-rands (cdr rands) env)]
      [else (errorf 'apply-k "Not a valid continuation: ~s" k*)])))

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
  (λ (env sym)
    (variant-case env
      [extended-env (formals args env)
        (if (memq sym formals)
            (apply-k (little-lookup sym formals args))
            (apply-env env sym))]
      [else (apply-k (global-table sym))])))


(define apply-closure
  (λ (proc args)
    (variant-case proc
      [closure (formals body env)
        ; (set! k* k*)
        (eval-exp body
          (make-extended-env formals args env))]
      [primitive (sym)
        ; (set! k* k*)
        (apply-k (apply-primitive sym args))]
      [continuation-closure (kont)
        (set! k* kont)
        (apply-k (car args))]
      [else (errorf 'apply-closure "Invalid closure type: ~s" proc)])))


;; This is a major hack!  We really shouldn't use scheme's
;; "apply", but instead have a giant case statement which switches on
;; sym and has in it the code for applying all the primitive
;; functions. 
(define apply-primitive
  (λ (sym args)
    (case sym
      [(zero?) (let ([x (apply (eval sym) args)])
                 (if x 1 0))]
      [else (apply (eval sym) args)])))


(define global-table
  (let ([apply* (make-primitive '*)]
        [apply+ (make-primitive '+)]
        [apply- (make-primitive '-)]
        [apply-zero? (make-primitive 'zero?)]
        [apply-cons (make-primitive 'cons)]
        [apply-car (make-primitive 'car)]
        [apply-cdr (make-primitive 'cdr)])
    (λ (sym)
      (case sym
        [(cons) apply-cons]
        [(car) apply-car]
        [(cdr) apply-cdr]
        [(zero?) apply-zero?]
        [(X) 10]
        [(V) 5]
        [(D) 500]
        [(C) 100]
        [(I) 1]
        [(M) 1000]
        [(*) apply*]
        [(+) apply+]
        [(-) apply-]
        [else
          (errorf 'global-table "unbound variable: ~s" sym)]))))

(define eval-rands
  (λ (rands env)
    (cond
      [(null? rands)
       ; (set! k* k*)
       (apply-k '())]
      [else
        (set! k* (make-post-first-rands-k rands env k*))
        (eval-exp (car rands) env)])))

(define eval-exp
  (letrec
    ([eval-exp
       (λ (e env)
         (variant-case e
           [lit (datum)
             ; (set! k* k*)
             (apply-k datum)]
           [varref (var)
             ; (set! k* k*)
             (apply-env env var)]
           [if (test-exp then-exp else-exp)
             (set! k* (make-post-test-k then-exp else-exp env k*))
             (eval-exp test-exp env)]
           [app (rator rands)
             (set! k* (make-post-rator-k rands env k*))
             (eval-exp rator env)]
           [letcc (var exp)
             ;; 在环境中绑定 var 为一个函数，当时的 k 会被丢弃，使用此时的 k
             ; (set! k* k*)
             (eval-exp exp (make-extended-env/1 var
                             (make-continuation-closure k*)
                             env))]
           [lambda (formals body)
             ; (set! k* k*)
             (apply-k (make-closure formals body env))]))])
    (λ (e env)
      ; (set! k* k*)
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
           [(and (list? e)
                 (eq? (car e) 'letcc))
            (make-letcc (cadr e)
              (parse-exp (caddr e)))]
           [else
             (make-app (parse-exp (car e))
               (map parse-exp (cdr e)))]))])
    (λ (unparsed-expression)
      (letrec
        ([loop (λ (pr)
                 (loop
                   (begin
                     (set! k* (car pr))
                     (apply-k* (cdr pr)))))])
        (letcc escape-to-scheme
          (loop
            (begin
              (set! k* (make-final-k escape-to-scheme))
              (eval-exp (parse-exp unparsed-expression)
                  global-table))))))))

#|
> (run
    '((lambda (n)
        ((lambda (!)
           (! n !))
         (lambda (n bang)
           (if (zero? n)
               1
               (* n (bang (- n 1) bang))))))
      5))
120
|#
