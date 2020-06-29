(load "record.ss")

;; k* 本质上就是堆栈，将其改成帧，原本每一次会保存新的 k，现在变为压栈。
;; 使用 list 表示堆栈，压栈就是 cons 操作，取出帧就是 car

(define k* 'nobinding)
(define acc* 'nobinding)
(define env* 'nobinding)
(define exp* 'nobinding)
(define rands* 'nobinding)
(define sym* 'nobinding)
(define proc* 'nobinding)
(define args* 'nobinding)

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
          (display (vector-ref (car k) 0))
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


(define-record post-test-frame (then-exp else-exp env))
(define-record post-rator-frame (rands env))
(define-record post-rands-frame (proc))
(define-record post-rest-rands-frame (a))
(define-record post-first-rands-frame (rands env))
(define-record final-frame (jumpout))


(define apply-k*
  (λ ()
    (show-k-trace k*)
    (let ([frame (car k*)])
      (set! k* (cdr k*))
      (variant-case frame
        [final-frame (jumpout) (jumpout acc*)]
        [post-test-frame (then-exp else-exp env)
          (if (zero? acc*)
              (begin
                (set! env* env)
                (set! exp* else-exp)
                (eval-exp))
              (begin
                (set! env* env)
                (set! exp* then-exp)
                (eval-exp)))]
        [post-rator-frame (rands env)
          (set! k* (cons (make-post-rands-frame acc*) k*))
          (set! env* env)
          (set! rands* rands)
          (eval-rands)]
        [post-rands-frame (proc)
          (set! proc* proc)
          (set! args* acc*)
          (apply-closure)]
        [post-rest-rands-frame (a)
          (set! acc* (cons a acc*))]
        [post-first-rands-frame (rands env)
          (set! k* (cons (make-post-rest-rands-frame acc*) k*))
          (set! env* env)
          (set! rands* (cdr rands))
          (eval-rands)]
        [else (errorf 'apply-frame "Not a valid continuation: ~s" frame)]))))

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
  (λ ()
    (variant-case env*
      [extended-env (formals args env)
        (if (memq sym* formals)
            (set! acc* (little-lookup sym* formals args))
            (begin
              (set! env* env)
              ; (set! sym* sym*)
              (apply-env)))]
      [else
        (set! acc* (global-table sym*))])))


(define apply-closure
  (λ ()
    (variant-case proc*
      [closure (formals body env)
        ; (set! k* k*)
        (set! env* (make-extended-env formals args* env))
        (set! exp* body)
        (eval-exp)]
      [primitive (sym)
        ; (set! k* k*)
        (set! acc* (apply-primitive sym args*))]
      [continuation-closure (kont)
        (set! k* kont)
        (set! acc* (car args*))]
      [else (errorf 'apply-closure "Invalid closure type: ~s" proc*)])))


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
  (λ ()
    (cond
      [(null? rands*)
       ; (set! k* k*)
       (set! acc* '())]
      [else
        (set! k* (cons (make-post-first-rands-frame rands* env*) k*))
        ; (set! env* env*)
        (set! exp* (car rands*))
        (eval-exp)])))

(define eval-exp
  (λ ()
    (variant-case exp*
      [lit (datum)
        ; (set! k* k*)
        (set! acc* datum)]
      [varref (var)
        ; (set! k* k*)
        ; (set! env* env*)
        (set! sym* var)
        (apply-env)]
      [if (test-exp then-exp else-exp)
        (set! k* (cons (make-post-test-frame then-exp else-exp env*) k*))
        ; (set! env* env*)
        (set! exp* test-exp)
        (eval-exp)]
      [app (rator rands)
        (set! k* (cons (make-post-rator-frame rands env*) k*))
        ; (set! env* env*)
        (set! exp* rator)
        (eval-exp)]
      [letcc (var exp)
        ;; 在环境中绑定 var 为一个函数，当时的 k 会被丢弃，使用此时的 k
        ; (set! k* k*)
        (set! env* (make-extended-env/1 var
                    (make-continuation-closure k*)
                    env*))
        (set! exp* exp)
        (eval-exp)]
      [lambda (formals body)
        ; (set! k* k*)
        (set! acc* (make-closure formals body env*))])))


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
        ([loop (λ ()
                 (apply-k*)
                 (loop))])
        (letcc escape-to-scheme
          (set! k* (cons (make-final-frame escape-to-scheme) '()))
          (set! env* global-table)
          (set! exp* (parse-exp unparsed-expression))
          (eval-exp)
          (loop))))))

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
