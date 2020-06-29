(load "record.ss")

;; 给 kcontinuations 增加一个 trace
;; closure 是 apply-k 的 continuation
;; k 是 eval-exp 的 continuation

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

(define-record extended-env (formals args env))
(define-record closure (formals body env))
(define-record primitive (sym))

(define-record post-test-k (then-exp else-exp env k))
(define-record post-rator-k (rands env k))
(define-record post-rands-k (proc k))
(define-record post-rest-rands-k (a k))
(define-record post-first-rands-k (rands env k))
(define-record final-k ())

(define apply-k
  (λ (k val)
    (show-k-trace k)
    (variant-case k
      [final-k () val]
      [post-test-k (then-exp else-exp env k)
        (if (zero? val)
            (eval-exp else-exp env k)
            (eval-exp then-exp env k))]
      [post-rator-k (rands env k)
        (eval-rands rands env
          (make-post-rands-k val k))]
      [post-rands-k (proc k)
        (apply-closure proc val k)]
      [post-rest-rands-k (a k)
        (apply-k k (cons a val))]
      [post-first-rands-k (rands env k)
        (eval-rands (cdr rands) env
          (make-post-rest-rands-k val k))]
      [else (errorf 'apply-k "Not a valid continuation: ~s" k)])))

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


(define apply-closure
  (λ (proc args k)
    (variant-case proc
      [closure (formals body env)
        (eval-exp body
          (make-extended-env formals args env) k)]
      [primitive (sym)
        (apply-k k (apply-primitive sym args))]
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
  (λ (rands env k)
    (cond
      [(null? rands) (apply-k k '())]
      [else (eval-exp (car rands) env
              (make-post-first-rands-k rands env k))])))

(define eval-exp
  (letrec
    ([eval-exp
       (λ (e env k)
         (variant-case e
           [lit (datum) (apply-k k datum)]
           [varref (var) (apply-env env var k)]
           [if (test-exp then-exp else-exp)
             (eval-exp test-exp env
               (make-post-test-k then-exp else-exp env k))]
           [app (rator rands)
             (eval-exp rator env
               (make-post-rator-k rands env k))]
           [lambda (formals body)
             (apply-k k
               (make-closure formals body env))]))])
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
        (make-final-k)))))

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
