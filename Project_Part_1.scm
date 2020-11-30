
;; Towards a Scheme Interpreter for the Lambda Calculus -- Part 1: Syntax

;; 5 points

;; Due December 1, and pre-requisite for all subsequent parts of the project

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All programming is to be carried out using the pure functional sublanguage of R5RS Scheme.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; You might want to have a look at http://www.cs.unc.edu/~stotts/723/Lambda/overview.html

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 1. The lambda calculus is a particularly simple programming language consisting only of
;; variable references, lambda expressions with a single formal parameter, and function
;; applications.  A BNF definition of lambda calculus expressions is

;; <expr> ::= <variable> | (lambda ( <variable> ) <expr> )  |  ( <expr> <expr> )

;; Design a data type for the lambda calculus, with constructors, selectors, and classifiers.

;; For concrete representation, use Scheme, as follows:  an identifier should be represented as
;; a quoted Scheme variable, a lambda expression (lambda (x) E) as the quoted 3-element list
;; '(lambda (x) [list representing E]), and an application  (E1 E2) as the quoted 2-element list
;; '([list representing E1]  [list representing E2])

; constructor

; lambda
(define (make-lambda variable expr)
  (list `lambda (list variable)  expr
        )
  )

; list of expr
(define (make-expr expr-1 expr-2)
  (list expr-1 expr-2))
; test for the constructor

(define test-lambda-ex1 (make-lambda  `x `a))
"this is test-lambda-ex1:"
test-lambda-ex1
(newline)
(define test-expr-ex1 (make-expr `a `b))
"this is test-expr-ex1:"
test-expr-ex1

(define test-make-expr (make-expr 'x (make-lambda 'x 'x)))
"this is test-make-expr"
test-make-expr


; selectors

(define (lambda-symbol expr)
  (car expr)
  )

(define (lambda-variable expr)
  (cadr expr)
  )

(define (lambda-body expr)
  (caddr expr))

; selectors for list of two E -> (E` E``)
(define (expr-1 expr)
  (car expr))

(define (expr-2 expr)
  (cadr expr))

;test case
(expr-1 test-make-expr)

; classifiers
(define (variable? expr)
  (symbol? expr)
  )

(define (lambda-symbol? expr)
  (and (list? expr)(equal? (lambda-symbol expr) `lambda))
  )

(define (lambda-body? expr)
  (or (list? expr) (not (equal? (lambda-symbol expr) `lambda)))
  )

; test case
(lambda-body? test-expr-ex1)



;; 2.  In (lambda (<variable>) <expr>), we say that <variable> is a binder that
;; binds all occurrences of that variable in the body, <expr>, unless some intervening
;; binder of the same variable occurs. Thus in (lambda (x) (x (lambda (x) x))),
;; the first occurrence of x binds the second occurrence of x, but not
;; the fourth.  The third occurrence of x binds the fourth occurrence of x.

;; A variable x occurs free in an expression E if there is some occurrence of x which is not
;; bound by any binder of x in E.  A variable x occurs bound in an expression E if it is
;; not free in E.  Thus x occurs free in (lambda (y) x), bound in (lambda (x) x), and both
;; free and bound in (lambda (y) (x (lambda (x) x))).

;; As a consequence of this definition, we can say that a variable x occurs free in a
;; lambda calculus expression E iff one of the following holds:

;;   (i) E = x
;;   (ii) E = (lambda (y) E'), where x is distinct from y and x occurs free in E'
;;   (iii) E = (E' E'') and x occurs free in E' or x occurs free in E''

;; Observe that this is an inductive definition, exploiting the structure of lambda calculus
;; expressions.

;; Similarly, a variable x occurs bound in a lambda calculus expression E iff one of the
;; following holds:

;;   (i) E = (lambda (x) E') and x occurs free in E'
;;   (ii) E = (lambda (y) E'), and x occurs bound in E': here, y may be x, or distinct from x
;;   (iii) E = (E1 E2) and x occurs bound in either E1 or E2

;; Develop and prove correct a procedure free-vars that inputs a list representing a lambda calculus
;; expression E and outputs a list without repetitions (that is, a set) of the variables occurring
;; free in E.

; ITERATIVE

; SPEC
;   pre: E -> a list representing a lambda calclus expression. ex: (lambda (y) x) or (lambda (x) (x (lambda (x) x)))
;   post: result -> a list of unique free variables from the input E

; CODE

; helper function

(define (remove-duplicates l)
        (define (helper lst element-so-far)
          (cond ((null? lst) element-so-far)
                ((member (car lst) (cdr lst)) (helper (cdr lst) element-so-far))
                (else (helper (cdr lst) (append element-so-far (list (car lst)))))
                )
          )
  (helper l `())
  )
"remove-duplicates `(a b a b c)"
(remove-duplicates `(a b a b c))

; main function
(define (free-vars E)
  (define (helper expr args vars-so-far)

    (cond ((null? expr) vars-so-far)
          ((variable? expr)
           (cond ((not (member expr args)) (append (list expr) vars-so-far))
                 (else vars-so-far))
           )
          ((lambda-symbol? expr)
           (helper (lambda-body expr) (append (lambda-variable expr) args) vars-so-far)
           )
          ((lambda-body? expr)
           (helper (expr-1 expr) args (append (helper (expr-2 expr) args vars-so-far) vars-so-far)))
          )
    )
  (remove-duplicates(helper E `() `()))
  )

; TEST
"test cases for free-vars"
"input: `()"
(free-vars `())
"input: (make-lambda `y `x)"
(free-vars (make-lambda `y `x))
"input: (make-lambda `y `y)"
(free-vars (make-lambda `y `y))
"input: (make-lambda `y (make-lambda `x `y))"
(free-vars (make-lambda `y (make-lambda `x `y)))
"input: (make-lambda `y (make-lambda `x `x))"
(free-vars (make-lambda `y (make-lambda `x `x)))
"input: (make-lambda `y (make-lambda `x `z))"
(free-vars (make-lambda `y (make-lambda `x `z)))
"input: (make-lambda `y (make-expr `x `z))"
(free-vars (make-lambda `y (make-expr `x `z)))
"input: (make-lambda `a (make-expr `b (make-lambda `b `c)))"
(free-vars (make-lambda `a (make-expr `b (make-lambda `b `c))))
"input: (make-lambda `a (make-expr `a (make-lambda `b `a)))"
(free-vars (make-lambda `a (make-expr `a (make-lambda `b `a))))
"input: (make-lambda `a (make-expr `b (make-lambda `c `b)))"
(free-vars (make-lambda `a (make-expr `b (make-lambda `c `b))))

; test cases given by professor
"professor test case 1 for free vars:"
(define lambda-exp1 '((lambda (x) (x (lambda (y) (lambda (x) (z (y x))))))
(lambda (u) (x y))))
lambda-exp1
(free-vars lambda-exp1)
"professor test case 2 for free vars:"
(define lambda-exp2 '(lambda (x) (x (lambda (y) (((lambda (u) (x y))(lambda (x) (z (y x))))
(lambda (w) (x y)))))))
lambda-exp2
(free-vars lambda-exp2)

; GUESS-INVATIANT TEST/PROOF
;
; Guess-invariant:
;
; Strong-enough?:
;
; Weak-enough?:
;
; Preserved?
; Current call:
; Next call:
;
; Termination:



;; Develop and prove correct a procedure bound-vars that inputs a list representing a lambda calculus
;; expression E and outputs the set of variables which occur bound in E.

; ITERATIVE

; SPEC
;   pre: E -> a list representing a lambda calclus expression. ex: (lambda (y) x) or (lambda (x) (x (lambda (x) x)))
;   post: result -> a list of unique free variables from the input E

; CODE

; main funciton

(define (bounded-vars E)
  (define (helper expr args vars-so-far)

    (cond ((null? expr) vars-so-far)
          ((variable? expr)
           (cond ((member expr args) (append (list expr) vars-so-far))
                 (else vars-so-far))
           )
          ; this is checking E = lambda (x) (E)
          ((lambda-symbol? expr)
           (helper (lambda-body expr) (append (lambda-variable expr) args) vars-so-far)
           )
          ; this is checking E = (E` E``)
          ((lambda-body? expr)
           (helper (expr-1 expr) args (append (helper (expr-2 expr) args vars-so-far) vars-so-far)))
          )
    )
  (remove-duplicates(helper E `() `()))
  )

; TEST

"test cases for bounded-vars"
"input: `()"
(bounded-vars `())
"input: (make-lambda `y `x)"
(bounded-vars (make-lambda `y `x))
"input: (make-lambda `y `y)"
(bounded-vars (make-lambda `y `y))
"input: (make-lambda `y (make-lambda `x `y))"
(bounded-vars (make-lambda `y (make-lambda `x `y)))
"input: (make-lambda `y (make-lambda `x `x))"
(bounded-vars (make-lambda `y (make-lambda `x `x)))
"input: (make-lambda `y (make-lambda `x `z))"
(bounded-vars (make-lambda `y (make-lambda `x `z)))
"input: (make-lambda `y (make-expr `x `z))"
(bounded-vars (make-lambda `y (make-expr `x `z)))
"input: (make-lambda `a (make-expr `b (make-lambda `b `c)))"
(bounded-vars (make-lambda `a (make-expr `b (make-lambda `b `c))))
"input: (make-lambda `a (make-expr `a (make-lambda `b `a)))"
(bounded-vars (make-lambda `a (make-expr `a (make-lambda `b `a))))
"input: (make-lambda `a (make-expr `b (make-lambda `c `b)))"
(bounded-vars (make-lambda `a (make-expr `b (make-lambda `c `b))))

; test cases given by professor
"professor test case 1 for bounded vars:"
lambda-exp1
(bounded-vars lambda-exp1)
"professor test case 2 for bounded vars:"
lambda-exp2
(bounded-vars lambda-exp2)


; GUESS-INVATIANT TEST/PROOF
;
; Guess-invariant:
;
; Strong-enough?:
;
; Weak-enough?:
;
; Preserved?
; Current call:
; Next call:
;
; Termination:


;; 3.  Define a function all-ids which returns the set of all symbols -- free or bound variables,
;; as well as the lambda identifiers for which there are no bound occurrences -- which occur in
;; a lambda calculus expression E.  

; ITERATIVE

; SPEC

; CODE

; main funciton

(define (all-ids E)
  (define (helper expr id-so-far)
    (cond ((null? expr) id-so-far)
          ((variable? expr) (append (list expr) id-so-far))
          ((lambda-symbol? expr)
           (helper (lambda-body expr) (append (lambda-variable expr) id-so-far))
           )
          ; this is checking E = (E` E``)
          ((lambda-body? expr)
           (helper (expr-1 expr) (append (helper (expr-2 expr) id-so-far) id-so-far)))
          )
    )

  (remove-duplicates(helper E `()))
  )

; TEST
"test cases for all-ids"
"input: `()"
(all-ids `())
"input: (make-lambda `y `x)"
(all-ids (make-lambda `y `x))
"input: (make-lambda `y `y)"
(all-ids (make-lambda `y `y))
"input: (make-lambda `y (make-lambda `x `y))"
(all-ids (make-lambda `y (make-lambda `x `y)))
"input: (make-lambda `y (make-lambda `x `x))"
(all-ids (make-lambda `y (make-lambda `x `x)))
"input: (make-lambda `y (make-lambda `x `z))"
(all-ids (make-lambda `y (make-lambda `x `z)))
"input: (make-lambda `y (make-expr `x `z))"
(all-ids (make-lambda `y (make-expr `x `z)))
"input: (make-lambda `a (make-expr `b (make-lambda `b `c)))"
(all-ids (make-lambda `a (make-expr `b (make-lambda `b `c))))
"input: (make-lambda `a (make-expr `a (make-lambda `b `a)))"
(all-ids (make-lambda `a (make-expr `a (make-lambda `b `a))))
"input: (make-lambda `a (make-expr `b (make-lambda `c `b)))"
(all-ids (make-lambda `a (make-expr `b (make-lambda `c `b))))

; test cases given by professor
"professor test case 1 for all-ids:"
lambda-exp1
(all-ids lambda-exp1)
"professor test case 2 for all-ids:"
lambda-exp2
(all-ids lambda-exp2)

; test cases given by professor


; GUESS-INVATIANT TEST/PROOF
;
; Guess-invariant:
;
; Strong-enough?:
;
; Weak-enough?:
;
; Preserved?
; Current call:
; Next call:
;
; Termination:

