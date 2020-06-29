(load "record.ss")
;; 单参数函数

(define lambda-expression?
  (λ (e)
    (and (list? e)
         (eq? (car e) 'lambda))))

; 找出 e 在 env 中的序号
(define find-lexical-address
  (λ (e cenv)
    (call/cc
      (λ (free-variable)
        (letrec
          ([find-lexical-address
             (λ (cenv)
               (cond
                 [(null? cenv)
                  (free-variable 'free)]
                 [(eq? (car cenv) e) 0]
                 [else (add1 (find-lexical-address (cdr cenv)))]))])
          (find-lexical-address cenv))))))

(define scope
  (λ (exp)
    (letrec
      ([scope (λ (e cenv)
                (cond
                  ; 变量
                  [(atom? e)
                   (list (find-lexical-address e cenv) ': e)]
                  ; 函数
                  [(lambda-expression? e)
                   (list 'lambda (car (cadr e))
                     (scope (caddr e)
                       (cons (car (cadr e)) cenv)))]
                  ; 调用
                  [else (list (scope (car e) cenv)
                          (scope (cadr e) cenv))]))])
      (scope exp '()))))

(define type-of
  (λ (sym)
    (λ (x)
      (and (pair? x)
           (eq? (car x) sym)))))

#|
> (scope '(((lambda (x)
              (lambda (y)
                x)) 1) 2))
(((lambda x (lambda y (1 : x))) (free : 1)) (free : 2))
|#
