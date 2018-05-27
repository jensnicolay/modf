#lang racket
(provide (all-defined-out))

(struct lattice (α γ ⊥ ⊔ ⊑ true? false? eq? global))

(struct prim2 (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                         (equal? (prim2-name s1) (prim2-name s2))))
                                                    (define hash-proc (lambda (s rhash) (equal-hash-code (prim2-name s))))
                                                    (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim2-name s))))))

(define %random (lambda (n) (if (zero? n) 0 (random n))))

;; conc lattice
(define (conc-α v)
  v)

(define (conc-γ v)
  (set v))

(define conc-⊥ "conc-⊥")

(define (conc-⊔ current new)
  (if (eq? new conc-⊥)
      current
      (if (eq? current conc-⊥)
          new
          (error "cannot join two non-bot values" current new))))

(define (conc-⊑ v1 v2)
  (or (eq? v1 conc-⊥)
      (eq? v1 v2)))
              
(define (conc-true? v)
  v)

(define (conc-false? v)
  (not v))

(define conc-eq? eq?)

(define conc-global
  
  `(("=" . ,(conc-α (prim2 "=" =)))
    ("<" . ,(conc-α (prim2 "<" <)))
    (">" . ,(conc-α (prim2 ">" >)))
    ("<=" . ,(conc-α (prim2 "<=" <=)))
    (">=" . ,(conc-α (prim2 ">=" >=)))
    ("+" . ,(conc-α (prim2 "+" +)))
    ("-" . ,(conc-α (prim2 "-" -)))
    ("*" . ,(conc-α (prim2 "*" *)))
    ("/" . ,(conc-α (prim2 "/" /)))
    ("not" . ,(conc-α (prim2 "not" not)))
    ;("and" . ,(conc-α (prim2 "and" (lambda l
                                     ;(for/fold ((res #t))
                                     ;          ((el l))
                                     ;  (and res el))))))
    ;("or" . ,(conc-α (prim2 "or" (lambda l
                                   ;(for/fold ((res #f))
                                   ;          ((el l))
                                   ;  (or res el))))))
    ("gcd" . ,(conc-α (prim2 "gcd" gcd)))
    ("modulo" . ,(conc-α (prim2 "modulo" modulo)))
    ("remainder" . ,(conc-α (prim2 "remainder" remainder)))
    ("quotient" . ,(conc-α (prim2 "quotient" quotient)))
    ("ceiling" . ,(conc-α (prim2 "ceiling" ceiling)))
    ("arithmetic-shift" . ,(conc-α (prim2 "arithmetic-shift" arithmetic-shift)))
    ("log" . ,(conc-α (prim2 "log" log)))
    ("sin" . ,(conc-α (prim2 "sin" sin)))
    ("cos" . ,(conc-α (prim2 "cos" cos)))
    ("sqrt" . ,(conc-α (prim2 "sqrt" sqrt)))
    ("expt" . ,(conc-α (prim2 "expt" expt)))
    ("max" . ,(conc-α (prim2 "max" max)))
    ("even?" . ,(conc-α (prim2 "even?" even?)))
    ("odd?" . ,(conc-α (prim2 "odd?" odd?)))
    ("symbol?" . ,(conc-α (prim2 "symbol?" symbol?)))
    ("null?" . ,(conc-α (prim2 "null?" null?)))
    ("char?" . ,(conc-α (prim2 "char?" char?)))
    ("printf" . ,(conc-α (prim2 "printf" printf)))
    ("integer?" . ,(conc-α (prim2 "integer?" integer?)))
    ("zero?" . ,(conc-α (prim2 "zero?" zero?)))
    ("number->string" . ,(conc-α (prim2 "number->string" number->string)))
    ("string?" . ,(conc-α (prim2 "string?" string?)))
    ("string->symbol" . ,(conc-α (prim2 "string->symbol" string->symbol)))
    ("string->number" . ,(conc-α (prim2 "string->number" string->number)))
    ("exact->inexact" . ,(conc-α (prim2 "exact->inexact" exact->inexact)))
    ("symbol->string" . ,(conc-α (prim2 "symbol->string" symbol->string)))
    ("integer->char" . ,(conc-α (prim2 "integer->char" integer->char)))
    ("string-length" . ,(conc-α (prim2 "string-length" string-length)))
    ("string-ref" . ,(conc-α (prim2 "string-ref" string-ref)))
    ;("list->string" . ,(conc-α (prim2 "list->string" list->string)))
    ;("pair?" . ,(conc-α (prim2 "pair?" pair?)))
    ("string-append" . ,(conc-α (prim2 "string-append" string-append)))
    ("char->integer" . ,(conc-α (prim2 "char->integer" char->integer)))
    ("char-alphabetic?" . ,(conc-α (prim2 "char-alphabetic?" char-alphabetic?)))
    ("char-numeric?" . ,(conc-α (prim2 "char-numeric?" char-numeric?)))
    ("char=?" . ,(conc-α (prim2 "char=?" char=?)))
    ("number?" . ,(conc-α (prim2 "number?" number?)))
    ("%random" . ,(conc-α (prim2 "%random" %random)))
    ("display" . ,(conc-α (prim2 "display" (lambda _ 'undefined)))) ; sym
    ("newline" . ,(conc-α (prim2 "newline" (lambda _ 'undefined)))) ; sym
    ))

(define conc-lattice (lattice conc-α conc-γ conc-⊥ conc-⊔ conc-⊑ conc-true? conc-false? conc-eq? conc-global))
;;

;; type lattice
(define NUM "NUM")
(define BOOL "BOOL")
(define STR "STR")
(define SYM "SYM")
(define CHAR "CHAR")

(define (type-α v)
  (cond
    ((number? v) (set NUM))
    ((boolean? v) (set BOOL))
    ((symbol? v) (set SYM))
    ((string? v) (set STR))
    ((char? v) (set CHAR))
    (else (set v))))

#|    
    ((clo? v) (set v))
    ((prim? v) (set v))
    ((prim2? v) (set v))
    ((addr? v) (set v))
    ((pair? v) (set v))
    ((null? v) (set v))
    (else (error "bwek" v))))
|#

(define (type-γ v)
  v)

(define type-⊥ (set))

(define type-⊔ set-union)

(define type-⊑ subset?)

(define (type-true? v)
  #t)

(define (type-false? v)
  #t)

(define (type-eq? v1 v2)
  (set BOOL))

(define type-global
  (let ((->bool
         (lambda vs
           (set BOOL)))
        (->num
         (lambda vs
           (set NUM)))
        (->str
         (lambda vs
           (set STR)))
        (->char
         (lambda vs
           (set CHAR)))
        (->sym
         (lambda vs
           (set SYM)))
        )
    `(("=" . ,(type-α (prim2 "=" ->bool)))
      ("<" . ,(type-α (prim2 "<" ->bool)))
      ("<=" . ,(type-α (prim2 "<=" ->bool)))
      (">" . ,(type-α (prim2 ">" ->bool)))
      (">=" . ,(type-α (prim2 ">=" ->bool)))
      ("+" . ,(type-α (prim2 "+" ->num)))
      ("-" . ,(type-α (prim2 "-" ->num)))
      ("*" . ,(type-α (prim2 "*" ->num)))
      ("/" . ,(type-α (prim2 "/" ->num)))
      ("not" . ,(type-α (prim2 "not" ->bool)))
      ;("and" . ,(type-α (prim2 "and" ->bool)))
      ;("or" . ,(type-α (prim2 "or" ->bool)))
      ("gcd" . ,(type-α (prim2 "gcd" ->num)))
      ("modulo" . ,(type-α (prim2 "modulo" ->num)))
      ("remainder" . ,(type-α (prim2 "remainder" ->num)))
      ("quotient" . ,(type-α (prim2 "quotient" ->num)))
      ("ceiling" . ,(type-α (prim2 "ceiling" ->num)))
      ("arithmetic-shift" . ,(type-α (prim2 "arithmetic-shift" ->num)))
      ("log" . ,(type-α (prim2 "log" ->num)))
      ("sin" . ,(type-α (prim2 "sin" ->num)))
      ("cos" . ,(type-α (prim2 "cos" ->num)))
      ("sqrt" . ,(type-α (prim2 "sqrt" ->num)))
      ("expt" . ,(type-α (prim2 "expt" ->num)))
      ("max" . ,(type-α (prim2 "max" ->num)))
      ("even?" . ,(type-α (prim2 "even?" ->bool)))
      ("odd?" . ,(type-α (prim2 "odd?" ->bool)))
      ("symbol?" . ,(type-α (prim2 "symbol?" ->bool)))
      ("null?" . ,(type-α (prim2 "null?" ->bool)))
      ("char?" . ,(type-α (prim2 "char?" ->bool)))
      ("%random" . ,(type-α (prim2 "%random" ->num)))
      ("integer?" . ,(type-α (prim2 "integer?" ->bool)))
      ("zero?" . ,(type-α (prim2 "zero?" ->bool)))
      ("random" . ,(type-α (prim2 "random" ->num)))
      ("string-length" . ,(type-α (prim2 "string-length" ->num)))
      ("string-ref" . ,(type-α (prim2 "string-ref" ->char)))
      ;("list->string" . ,(type-α (prim2 "list->string" ->str)))
      ("number?" . ,(type-α (prim2 "number?" ->bool)))
      ("number->string" . ,(type-α (prim2 "number->string" ->str)))
      ("string?" . ,(type-α (prim2 "string?" ->bool)))
      ("string->symbol" . ,(type-α (prim2 "string->symbol" ->sym)))
      ("string->number" . ,(type-α (prim2 "string->number" ->num)))
      ("exact->inexact" . ,(type-α (prim2 "exact->inexact" ->num)))
      ("symbol->string" . ,(type-α (prim2 "symbol->string" ->str)))
      ("integer->char" . ,(type-α (prim2 "integer->char" ->char)))
      ;("list?" . ,(type-α (prim2 "list?" any->bool)))
      ;("pair?" . ,(type-α (prim2 "pair?" any->bool)))
      ("string-append" . ,(type-α (prim2 "string->append" ->str)))
      ("char->integer" . ,(type-α (prim2 "char->integer" ->num)))
      ("char-alphabetic?" . ,(type-α (prim2 "char-alphabetic?" ->bool)))
      ("char-numeric?" . ,(type-α (prim2 "char-numeric?" ->bool)))
      ("char=?" . ,(type-α (prim2 "char=?" ->bool)))
      ("display" . ,(type-α (prim2 "display" ->sym))) ; sym?
      ("newline" . ,(type-α (prim2 "newline" ->sym))) ; sym?
  )))

(define type-lattice (lattice type-α type-γ type-⊥ type-⊔ type-⊑ type-true? type-false? type-eq? type-global))
;;

;; points-to lattice
(define PRIM "PRIM")

(define (pt-α v)
  (cond
    ((number? v) (set PRIM))
    ((boolean? v) (set PRIM))
    ((symbol? v) (set PRIM))
    ((string? v) (set PRIM))
    ((char? v) (set PRIM))
    (else (set v))))

#|    
    ((clo? v) (set v))
    ((prim? v) (set v))
    ((prim2? v) (set v))
    ((addr? v) (set v))
    ((pair? v) (set v))
    ((null? v) (set v))
    (else (error "bwek" v))))

|#

(define (pt-eq? v1 v2)
  (set PRIM))

(define pt-global
  (let ((->prim
         (lambda vs
           (set PRIM))))
    `(("=" . ,(pt-α (prim2 "=" ->prim)))
      ("<" . ,(pt-α (prim2 "<" ->prim)))
      ("<=" . ,(pt-α (prim2 "<=" ->prim)))
      (">" . ,(pt-α (prim2 ">" ->prim)))
      (">=" . ,(pt-α (prim2 ">=" ->prim)))
      ("+" . ,(pt-α (prim2 "+" ->prim)))
      ("-" . ,(pt-α (prim2 "-" ->prim)))
      ("*" . ,(pt-α (prim2 "*" ->prim)))
      ("/" . ,(pt-α (prim2 "/" ->prim)))
      ("not" . ,(pt-α (prim2 "not" ->prim)))
      ;("and" . ,(pt-α (prim2 "and" ->prim)))
      ;("or" . ,(pt-α (prim2 "or" ->prim)))
      ("gcd" . ,(pt-α (prim2 "gcd" ->prim)))
      ("modulo" . ,(pt-α (prim2 "modulo" ->prim)))
      ("remainder" . ,(pt-α (prim2 "remainder" ->prim)))
      ("quotient" . ,(pt-α (prim2 "quotient" ->prim)))
      ("ceiling" . ,(pt-α (prim2 "ceiling" ->prim)))
      ("log" . ,(pt-α (prim2 "log" ->prim)))
      ("sin" . ,(pt-α (prim2 "sin" ->prim)))
      ("cos" . ,(pt-α (prim2 "cos" ->prim)))
      ("sqrt" . ,(pt-α (prim2 "sqrt" ->prim)))
      ("expt" . ,(pt-α (prim2 "expt" ->prim)))
      ("even?" . ,(pt-α (prim2 "even?" ->prim)))
      ("odd?" . ,(pt-α (prim2 "odd?" ->prim)))
      ("symbol?" . ,(pt-α (prim2 "symbol?" ->prim)))
      ("null?" . ,(pt-α (prim2 "null?" ->prim)))
      ("char?" . ,(pt-α (prim2 "char?" ->prim)))
      ("%random" . ,(pt-α (prim2 "%random" ->prim)))
      ("integer?" . ,(pt-α (prim2 "integer?" ->prim)))
      ("zero?" . ,(pt-α (prim2 "zero?" ->prim)))
      ("random" . ,(pt-α (prim2 "random" ->prim)))
      ("string-length" . ,(pt-α (prim2 "string-length" ->prim)))
      ("string-ref" . ,(pt-α (prim2 "string-ref" ->prim)))
      ;("list->string" . ,(pt-α (prim2 "list->string" ->prim)))
      ("number?" . ,(pt-α (prim2 "number?" ->prim)))
      ("number->string" . ,(pt-α (prim2 "number->string" ->prim)))
      ("string?" . ,(pt-α (prim2 "string?" ->prim)))
      ("string->symbol" . ,(pt-α (prim2 "string->symbol" ->prim)))
      ("string->number" . ,(pt-α (prim2 "string->number" ->prim)))
      ("exact->inexact" . ,(pt-α (prim2 "exact->inexact" ->prim)))
      ("symbol->string" . ,(pt-α (prim2 "symbol->string" ->prim)))
      ("integer->char" . ,(pt-α (prim2 "integer->char" ->prim)))
      ;("list?" . ,(type-α (prim2 "list?" any->bool)))
      ;("pair?" . ,(type-α (prim2 "pair?" any->bool)))
      ("string-append" . ,(pt-α (prim2 "string->append" ->prim)))
      ("char->integer" . ,(pt-α (prim2 "char->integer" ->prim)))
      ("char-alphabetic?" . ,(pt-α (prim2 "char-alphabetic?" ->prim)))
      ("char-numeric?" . ,(pt-α (prim2 "char-numeric?" ->prim)))
      ("char=?" . ,(pt-α (prim2 "char=?" ->prim))))))

(define pt-lattice (lattice pt-α type-γ type-⊥ type-⊔ type-⊑ type-true? type-false? pt-eq? pt-global))
