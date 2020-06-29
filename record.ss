(define-syntax λ
  (syntax-rules ()
    [(_ arg* bd bd* ...)
      (lambda arg* bd bd* ...)]))

;; (define-record name (field ...))
(define-syntax define-record
  (letrec ([build-name
             (λ (tem . args)
               (datum->syntax tem
                 (string->symbol
                   (apply string-append
                     (map (λ (x)
                            (if (string? x)
                                x
                                (symbol->string (syntax->datum x))))
                       args)))))])
    (λ (x)
      (syntax-case x ()
        [(_ name (field ...))
          (and (identifier? #'name)
               (andmap identifier? #'(field ...)))
          (with-syntax
            ([maker (build-name #'name "make-" #'name)]
             [pred (build-name #'name #'name "?")]
             [(acc ...)
               (map (λ (f) (build-name f #'name "-" f))
                 #'(field ...))]
             [(mut ...)
               (map (λ (f) (build-name f "set-" #'name "-" f "!"))
                 #'(field ...))]
             [len (add1 (length (syntax->list #'(field ...))))]
             [(index ...)
               (let loop ([n 1] [ls #'(field ...)])
                 (if (null? ls)
                     '()
                     (cons n (loop (add1 n) (cdr ls)))))])
            #'(begin
               (define maker
                 (λ (field ...)
                   (vector 'name field ...)))
               (define pred
                 (λ (obj)
                   (and (vector? obj)
                        (= (vector-length obj) len)
                        (eq? (vector-ref obj 0) 'name))))
               (define acc
                 (λ (obj)
                   (if (pred obj)
                       (vector-ref obj index)
                       (errorf 'acc "~s is not a ~s record" obj 'name))))
               ...
               (define mut
                 (λ (obj newval)
                   (if (pred obj)
                       (vector-set! obj index newval)
                       (errorf 'mut "~s is not a ~s record" obj 'name))))
               ...))]))))

;; (variant-case exp0 (name (field ...) exp1 exp2 ...) ...)
(define-syntax variant-case
  (let ([build-name
          (λ (tem . args)
            (datum->syntax tem
              (string->symbol
                (apply string-append
                  (map (λ (x)
                         (if (string? x)
                             x
                             (symbol->string (syntax->datum x))))
                    args)))))])
    (λ (x)
      (syntax-case x (else)
        [(_ thing clause ...)
          (not (identifier? #'thing))
          #'(let ([v thing])
             (variant-case v clause ...))]
        [(_ v)
          (syntax (errorf 'variant-case "No matching clause for ~s" v))]
        [(_ v (else exp0 exp1 ...))
          #'(begin exp0 exp1 ...)]
        [(_ v (name (field ...) exp0 exp1 ...) clause ...)
          (and (identifier? #'name)
               (andmap identifier? #'(field ...)))
          (with-syntax
            ([pred (build-name #'name #'name "?")]
             [(acc ...)
               (map (λ (x) (build-name x #'name "-" x))
                 (syntax->list #'(field ...)))])
            #'(if (pred v)
                  (let ([field (acc v)] ...)
                    exp0 exp1 ...)
                  (variant-case v clause ...)))]))))

(define-syntax letcc
  (syntax-rules ()
    [(& var b0 b1 ...)
     (call/cc (lambda (var) b0 b1 ...))]))
