(load "record.ss")

(define-record varref (var))
(define-record lambda (formals body))
(define-record app (rator rands))


(define scope
  (λ (exp)
    (letrec
      ([scope 
         (λ (pe cenv)
           (variant-case pe
             [varref (var)
               (list (find-lexical-address var cenv) ': var)]
             [lambda (formals body)
               (list 'lambda formals (scope body (cons formals cenv)))]
             [app (rator rands)
               (cons (scope rator cenv)
                 (map (λ (x) (scope x cenv))
                   rands))]))]
       [find-lexical-address
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
                         (find-lexical-address (cdr cenv) (add1 n))]))]
                  [find-lexical-address-ONE
                    (λ (e cenv)
                      (letrec
                        ([find-lexical-address
                           (λ (cenv)
                             (cond
                               [(eq? (car cenv) e) 0]
                               [else (add1 (find-lexical-address (cdr cenv)))]))])
                        (find-lexical-address cenv)))])
                 (find-lexical-address cenv 0)))))]
       [parse-exp
         (λ (e)
           (cond
             [(atom? e) (make-varref e)]
             [(and (list? e)
                   (eq? (car e) 'lambda))
              (make-lambda (cadr e) (parse-exp (caddr e)))]
             [else
              (make-app (parse-exp (car e))
                (map parse-exp (cdr e)))]))])
      (scope (parse-exp exp) '()))))

(define type-of
  (λ (sym)
    (λ (x)
      (and (pair? x)
           (eq? (car x) sym)))))
