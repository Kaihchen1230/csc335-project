;; Towards a Scheme Interpreter for the Lambda Calculus -- Part 2: Substitution

;; 8 points

;; Due December 8, and pre-requisite for all subsequent parts of the project


;; We have been talking about substitution throughout this semester - in the guise of the substitution rule
;; we use to compute the application of functions.  It turns out that substitution is the fundamental
;; operation of computation in the lambda calculus.  

;; In this part of our project, you will write a function subst which inputs a lambda calculus expression e1,
;; a variable v, and another lambda calculus expression e2, and which returns the lambda calculus expression
;; obtained from e1 by replacing all free occurrences of v by e2 in a way which avoids 'capturing'.  Let me
;; take a moment to describe capturing. 

;; I take for granted that you know that changing the name of a bound variable should not change the
;; meaning of a lambda calculus expression: for example, (lambda (x) x) has the same meaning as
;; (lambda (y) y), and
;;              (*) (lambda (x) (x (x w)))
;; has the same meaning as
;;              (**) (lambda (y) (y (y w))).
;; But suppose we substitute x for w in each of (*) and (**). The first substitution gives
;;                   (lambda (x) (x (x x))),
;; and the second substitution gives
;;                   (lambda (y) (y (y x)))
;; the first an expression with no free variables, while x is still free in the second.  These
;; do not have the same meaning -- that is, they are not logically equivalent.

;; (You might want to review the notion of logical equivalence from your discrete math notes.)

;; We say, in the first case, that the variable x has been captured by the binder, (lambda (x) ).

;; The problem occurs when we substitute more complex lambda expressions as well -- if, instead of
;; x, we substitute (lambda (z) (z x)) for w in (*), we obtain (lambda (x) (x (x (lambda (z) (z x))))) --
;; where the free x in (lambda (z) (z x)) has been captured.

;; Capturing is a bad thing: the way to avoid it is to change the bound variables before
;; carrying out the substitution.  Noting, for example, that x occurs free in (lambda (z) (z x)),
;; one sure way of accomplishing this is to change the bound variable x in (*) to a variable
;; which does not occur either in (*) or in (lambda (z) (z x)).  Thus the new variable might be
;; x0 -- anything not in the set {x, w, z}.


;; (Question: do we really need to avoid z in this case?)

;; Question: how do we generate a new variable?

;; Answer: using the all-ids function from Part 1, we have

;;; pre: exp is a lambda expression and str is a string, such as "x"

;;; post: (new-var exp "x") returns a symbol, perhaps x0, which does not occur in exp

(define (new-var lambda-exp str)
  (define old-vars (all-ids lambda-exp))
  (define (iter n)
    (let ((new (string->symbol (string-append str (number->string n)))))
      (cond ((not (element-of? new old-vars)) new)
            (else (iter (+ n 1))))))
  (iter 0))


;; Here string->symbol, string-append and number->string are Scheme primitives; you can implement
;; the function element-of yourself.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here is the assignment:


;; Design, write, and prove correct the function subst described in the second paragraph.


;; Here are some examples for you to try with your code:


;; (subst '(lambda (x) x) 'y 'x) returns (lambda (x) x)  -- no free occurrence of x the first argument

;; (subst '(lambda (x) x) '(x y) 'x)  returns (lambda (x) x) -- no free occurrence of x in the first argument

;; (subst '(lambda (x) (x y)) '(x y) 'x) gives (lambda (x) (x y)) -- no free occurrence of x in the first argument

;; (subst '(lambda (x) (x y)) '(x y) 'y)  gives (lambda (x0) (x0 (x y))) -- avoiding capture of x

;; (subst '(lambda (x) (x y (lambda (x) (x z)))) '(x y) 'y) gives
;;    (lambda (x0) (x0 (x y) (lambda (x) (x z)))) -- only the outer binder causes a problem

;; (subst '(lambda (x) (x y (lambda (x) (x y)))) '(x y) 'y) gives
;;    (lambda (x0) (x0 (x y) (lambda (x0) (x0 (x y))))) -- no need for two new variables

;; (subst '(lambda (x) (x y (lambda (y) (x (lambda (z) (x (y z))))))) '(x (y z)) 'y)  gives
;;    (lambda (x0) (x0 (x (y z)) (lambda (y) (x0 (lambda (z) (x0 (y z)))))))

;; (subst '(lambda (x) (x (y (lambda (y) (x (lambda (z) (x (y z)))))))) '(x (y z)) 'y)  gives
;;    (lambda (x0) (x0 ((x (y z)) (lambda (y) (x0 (lambda (z) (x0 (y z))))))))

;; (subst '(lambda (x) (x (w (lambda (y) (x (w (lambda (z) (x (y w))))))))) '(x (y z)) 'w) gives
;;    (lambda (x0) (x0 ((x (y z)) (lambda (x1) (x0 ((x (y z)) (lambda (x2) (x0 (x1 (x (y z)))))))))))

;; (subst '((lambda (x) (x y)) (lambda (y) (x y))) 'z 'x) gives
;;    ((lambda (x) (x y)) (lambda (y) (z y))

