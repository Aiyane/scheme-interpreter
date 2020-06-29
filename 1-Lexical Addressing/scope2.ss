(load "record.ss")
;; 多参数函数

(define lambda-expression?
  (λ (e)
    (and (list? e)
         (eq? (car e) 'lambda))))

(define find-lexical-address-ONE
  (λ (e cenv)
    (letrec
      [(find-lexical-address
         (λ (cenv)
           (cond
             [(eq? (car cenv) e) 0]
             [else
               (add1 (find-lexical-address (cdr cenv)))])))]
      (find-lexical-address cenv))))

; 找出 e 在 env 中的序号
(define find-lexical-address
  (λ (e cenv)
    (call/cc
      (λ (free-variable)
        (letrec
          ([find-lexical-address
             (λ (cenv n)
               (cond
                 [(null? cenv)
                  (free-variable 'free)]
                 [(memq e (car cenv))
                  (list n (find-lexical-address-ONE e (car cenv)))]
                 [else
                  (find-lexical-address (cdr cenv) (add1 n))]))])
          (find-lexical-address cenv 0))))))

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
                   (list 'lambda (cadr e)
                     (scope (caddr e)
                       (cons (cadr e) cenv)))]
                  ; 调用
                  [else (cons (scope (car e) cenv)
                          (map (λ (x) (scope x cenv))
                            (cdr e)))]))])
      (scope exp '()))))

(define type-of
  (λ (sym)
    (λ (x)
      (and (pair? x)
           (eq? (car x) sym)))))

#|
> (scope '(((lambda (x y)
              (lambda (z k) y)) 1 2) 3 4))
(((lambda (x y) (lambda (z k) ((1 1) : y)))
   (free : 1)
   (free : 2))
  (free : 3)
  (free : 4))
|#
