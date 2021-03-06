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
"selector -> lambda-body for test-lambda-ex1 = (lambda (x) a)"
(lambda-body test-lambda-ex1)

; classifiers
(define (variable? expr)
  (symbol? expr)
  )

(define (lambda-symbol? expr)
  (and (list? expr)(equal? (lambda-symbol expr) `lambda))
  )

(define (lambda-body? expr)
  (and (list? expr) (not (equal? (lambda-symbol expr) `lambda)))
  )

; test case
"clasifiers -> lambda-symbol? for test-lambda-ex1 = (lambda (x) a)"
(lambda-symbol? test-lambda-ex1)



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

; DEVELOPMENT
;   The idea is to cdr down the list, i.e. to go through each element of the list.
;   If we be more specific, then we will need to append an elemnent to our new list if that elemnent is not in the list.
;   And to check whether the element is in the list or not, we use the internal auxilliary function
;   means it returns #t if there is no duplicate.
;   So after we process the list with all the elements, we will return the list without any duplicates and with the unique free variables.

;   while developing this logic, it seems to make sense so far. Also the induction seems to make sense!
;   After some HEAVY-THINKING, we are ready to code and test cases. If anything doesn't seem to work, then we will propose changes as we go.

; SPEC
;   pre: E -> a list representing a lambda calclus expression based on the BNF definition from question 1. ex: (lambda (y) x) or (lambda (x) (x (lambda (x) x)))
;   post: result -> a list of unique free variables from the input E

; CODE

; helper function

; SPEC for remove-duplicates
;   pre: l -> a list
;   post: result -> a list of unique elements from the input l

; is-in?
; pre-condition: e is an element, lt is a list
; post-condition: returns #t if e occurs in the lst, #f otherwise

(define (removeDuplicates lst)
  (define (is-in? e lt)
    (cond ((null? lt) #f)
          (else (if (equal? e (car lt))
                    #t
                    (is-in? e (cdr lt))))))
  (define (iter lt result)
    (cond ((null? lt) result)
          (else (if (is-in? (car lt) result)
                    (iter (cdr lt) result)
                    (iter (cdr lt) (append result (list (car lt))))))))
  (iter lst '()))

; TEST (all cases passed)

(removeDuplicates '())
(removeDuplicates '(a))
(removeDuplicates '(a a))
(removeDuplicates '(a b a))
(removeDuplicates '(a a a a a b))
(removeDuplicates '(c a a a a a))
(removeDuplicates '(1 2 1 2 2 1 1 3 1 2))
; NOTE: internal is-in? function has been tested with ALL TEST PASSED
;(is-in? 'a '())
;(is-in? 'a '(b))
;(is-in? 'a '(a b c d))
;(is-in? 'a '(b d a d))
;(is-in? 'a '(b fd a))
;(is-in? '1 '(2 4 412 a 3))


; Now we assume that the helper function works as our pre-condition is satisfied each time we have called it. Therefore, it should return the post condition.


; GUESS-INVATIANT TEST/PROOF for remove-duplicates
;
; Guess-invariant: lst-all-unique-elements = (car lst) + lst-result + remove-duplicates(lst-remaining) if (car lst) not in lst-result
;
;                  in the program: lst-result = result

; Exit test: The program will halt if we have no elements.

; therefore, removeDuplicates(LST) = (append result removeDuplicates(lt))
; ->
; removeDuplicates(LST) = (append result '()) = result
; We got LST as the result with all the duplicates removed.

; Initial test: On the first call, lt = LST, and result = '()
; removeDuplicate(LST) = (append result removeDuplicate(lt))
; ->
; removeDuplicate(LST) = (append '() removeDuplicate(lt))
; = removeDuplicate(lst)
; We will start processing the elements after this.

; Current+next Test:
; Current Call: On the current call, removeDuplicate(LST) = (append result removeDuplicate(lt))
; Next Call: On the next call, we see if (car lt) is in result and if it is, we don't append it to result, else append to result.
; therefore, removeDuplicate(LST) = (append result removeDuplicate(lt))
; ->
; removeDuplicate(LST) = (append result removeDuplicate((cdr lt)))
; here if we add the element, then our result is (append result (car lt))).
; Therefore, considering what we got from the last call, this call works.
;
; Strong-enough?:
; When the program halts, we reaches to the end of the l -> `(), meaning the program went throught all the elements in l
; and add all the unique elements to the lst-result.
; GI: lst-all-unique-elements = (car lst) + lst-result + remove-duplicates(lst-remaining) if (car lst) not in lst-result
; ->
; lst-all-unique-elements = (car lst) + lst-result + remove-duplicates(None), since every list in scheme ended with `(), so `() won't be added to lst-result
; -> lst-all-unique-elements = lst-result
;
; Weak-enough?:
; In the first call we make to helper, the vars-so-far = `() -> an empty list
; and list-remaining is still l, the program hasn't processed any element yet. So, (car lst) is nothing, because the program hasn't started yet.
; GI: lst-all-unique-elements = (car lst) + lst-result + remove-duplicates(lst-remaining) if (car lst) not in lst-result
; ->
; lst-all-unique-elements = None + `() + remove-duplicates(lst-remaining)
; lst-all-unique-elements = remove-duplicates(lst-remaining)
; = remove-duplicates(lst-remaining)
;
; Preserved?
; Current call: Assume that the current call works, such that it works for the k elements in the input l
;               and lst-result stored all unique elements within the k elements.
; Next call: In the next call, we already have all the unique elements within the k elements of l from the last call (Current call). Now, we take
;            the next element through (car l) in the input l and check
;            1) if it is in the lst-result, then nothing will be added to the lst-result.
;            Then we take the last element in the input l, since the last element of every list is `(), so the lst-result is the all unique elements in the input l;
;            GI: lst-all-unique-elements =  (car lst) + lst-result + remove-duplicates(lst-remaining) if (car lst) not in lst-result
;            ->
;            lst-all-unique-elements =  None + lst-result + remove-duplicates(`()) since current element already existed in lst-result
;             ->  lst-all-unique-elements = lst-result
;
;           2) if it is not in the lst-result, then the it will be added to the lst-result
;           Then we take the last element in the input l, since the last element of every list is `(), so the lst-result is the all unique elements in the input l;
;           GI: lst-all-unique-elements =  (car lst) + lst-result + remove-duplicates(lst-remaining) if (car lst) not in lst-result
;           ->
;           lst-all-unique-elements = (car lst) + lst-result + remove-duplicates(`()) since current element doesn't existed in lst-result
;           ->  lst-all-unique-elements = lst-result
;
; Termination: According to the code, the program halts when the input l is empty, that is l = `(). As each call to helper function, the amount of elements
;              in l decease by 1. Eventually, l would be `(). Therefore, assuming the pre-condition holds, the program must eventually terminate.
;
; main function for free-vars
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
          ; check for (E` E``)
          ((lambda-body? expr)
           (helper (expr-1 expr) args (append (helper (expr-2 expr) args vars-so-far) vars-so-far)))
          )
    )
  (remove-duplicates(helper E `() `()))
  )


; TEST
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
; Guess-invariant: lst-all-free-vars = lst-result + free-vars(body-of-E)
;                  where lst-result = lst-result + E, if E is a variable and E is not defined in the parameters
;                  in the program, lst-result is vars-so-far and I am also using args to store the list of occuring parameters in E
;
; Strong-enough?:
; When the program halts, the program reaches to the last variable in the input E,
; then the program checks if last variable is not part of the parameters. If it is, then add to the lst-result, otherwise it won't be added to lst-result.
; GI: lst-all-free-vars = lst-result + free-vars(body-of-E)
;      where lst-result = lst-result + E, if E is a variable and E is not defined in the parameters
; 1) if E is not part of the parameters:
;    -> GI: lst-all-free-vars = E + lst-result + free-vars(None)
;       ->  lst-all-free-vars = lst-result
; 2) if E is part of the parameters:
;    -> GI: lst-all-free-vars = lst-result + free-vars(None)
;       ->  lst-all-free-vars = lst-result
;
; Weak-enough?:
; In the first call the program make to the helper function, the vars-so-far = `() -> an empty list, the parameters = `()
; and body of E is still E.
; GI: lst-all-free-vars = lst-result + free-vars(body of E)
;      where lst-result = lst-result + E, if E is a variable and E is not defined in the parameters
; -> lst-all-free-vars = `() + free-vars(E)
; -> lst-all-free-vars = free-vars(E)
;
; Preserved?
; Current call: Assume that the current call works, such that it works for the k amount of free variables in the input E. So, the lst-result stored
;               all k free variables at this point.
; Next call: In the next call, we assumed that we have working k amount of free variables in the input E from the last call (current call,
;            we will need the cases because we process the different structures of lambda differenty.
;            1) if it is null, we return the empty lst.
;            
;            GI: lst-all-free-vars = E + lst-result + free-vars(None)
;            ->  lst-all-free-vars = lst-result
;
;           2) For a variable case, we check if it is a member. If it is not a member, then we return an empty list. If lst is a member of
;              vars-so-far
;              if it is, return '() parameter
;              else return lst   (which will append it in the last call
;            -> GI: lst-all-free-vars = lst-result + free-vars(None)
;            ->  lst-all-free-vars = lst-result
;
;           3) If it is a lambda expression, we check if the variable of the lambda is a member or we can do a union on the vars-so-far and then recurse on the body.


; Termination:  The program will terminate, if we have the empty list. And everytime we go through the body of the lambda function,
;               Therefore, assuming that the pre-condition holds, the program must terminate. 



;; Develop and prove correct a procedure bound-vars that inputs a list representing a lambda calculus
;; expression E and outputs the set of variables which occur bound in E.

; ITERATIVE

; SPEC
;   pre: E -> a list representing a lambda calclus expression based on the BNF definition from question 1. ex: (lambda (y) x) or (lambda (x) (x (lambda (x) x)))
;   post: result -> a list of unique bounded variables from the input E. ex: (x)

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
; test cases given by professor
"professor test case 1 for bounded vars:"
lambda-exp1
(bounded-vars lambda-exp1)
"professor test case 2 for bounded vars:"
lambda-exp2
(bounded-vars lambda-exp2)


; GUESS-INVATIANT TEST/PROOF
;
; Guess-invariant: lst-all-bounded-vars = lst-result + bounded-vars(body-of-E)
;                  where lst-result = lst-result + E, if E is a variable and E is not defined in the parameters
;                  in the program, lst-result is vars-so-far and I am also using args to store the list of occuring parameters in E
;
; Strong-enough?:
; When the program halts, the program reaches to the last variable in the input E,
; then the program checks if last variable is not part of the parameters. If it is, then add to the lst-result, otherwise it won't be added to lst-result.
; GI: lst-all-bounded-vars = lst-result + bounded-vars(body-of-E)
;      where lst-result = lst-result + E, if E is a variable and E is not defined in the parameters
; 1) if E is not part of the parameters:
;    -> GI: lst-all-bounded-vars = E + lst-result + bounded-vars(None)
;       ->  lst-all-bounded-vars = lst-result
; 2) if E is part of the parameters:
;    -> GI: lst-all-bounded-vars = lst-result + bounded-vars(None)
;       ->  lst-all-bounded-vars = lst-result
;
; Weak-enough?:
; In the first call the program make to the helper function, the element-so-far = `() -> an empty list, the parameters = `()
; and body of E is still E.
; GI: lst-all-bounded-vars = lst-result + bounded-vars(body of E)
;      where lst-result = lst-result + E, if E is a variable and E is defined in the parameters
; -> lst-all-bounded-vars = `() + bounded-vars(E)
; -> lst-all-bounded-vars = bounded-vars(E)
;
; Preserved?
; Current call: Assume that the current call works, such that it works for the k amount of bounded variables in the input E. So, the lst-result stored
;               all k bounded variables at this point.
; Next call: In the next call, we assumed that we have working k amount of bounded variables in the input E from the last call (current call,
;            we will need the cases because we process the different structures of lambda differenty.
;            1) if it is null, we return the empty lst.
;            
;            GI: lst-all-bounded-vars = E + lst-result + bounded-vars(None)
;            ->  lst-all-bounded-vars = lst-result
;
;           2) For a variable case, we check if it is a member of the parameter. If it is not a member, then we return an vars-so-far. If lst is a member,
;              we add the variable to vars-so-far
;               GI: lst-all-bounded-vars = E + lst-result + bounded-vars(None)
;            ->  lst-all-bounded-vars = vars-so-far + bounded-var 
;            
;
;           3) If it is a lambda expression, we check if the variable of the lambda is a member or we can do a union on the vars-so-far and then recurse on the body.


; Termination:  The program will terminate, if we have the empty list. And everytime we go through the body of the lambda function,
;               Therefore, assuming that the pre-condition holds, the program must terminate. 


;; 3.  Define a function all-ids which returns the set of all symbols -- free or bound variables,
;; as well as the lambda identifiers for which there are no bound occurrences -- which occur in
;; a lambda calculus expression E.  

; ITERATIVE

; SPEC
;   pre: E -> a list representing a lambda calclus expression based on the BNF definition from question 1. ex: (lambda (y) x) or (lambda (x) (x (lambda (x) x)))
;   post: result -> a list of unique free variables, bounded variables and lambda identifiers from the input E

; CODE

; main funciton

(define (all-ids E)
  (define (helper expr id-so-far)
    (cond ((null? expr) id-so-far)
          ((variable? expr) (append id-so-far (list expr)))
          ((lambda-symbol? expr)
           (helper (lambda-body expr) (append id-so-far (lambda-variable expr)))
           )
          ; this is checking E = (E` E``)
          ((lambda-body? expr)
           (helper (expr-1 expr) (append id-so-far (helper (expr-2 expr) id-so-far))))
          )
    )

  (remove-duplicates(helper E `()))
  )

; TEST

; test cases given by professor
"professor test case 1 for all-ids:"
lambda-exp1
(all-ids lambda-exp1)
"professor test case 2 for all-ids:"
lambda-exp2
(all-ids lambda-exp2)


; GUESS-INVATIANT TEST/PROOF
;
; Guess-invariant: lst-of-all-ids = lst-result + all-ids(body-of-E)
;                  where lst-result = lst-result + E, if E is a variable
;                  in the program, lst-result is id-so-far
;
; Strong-enough?:
; When the program halts, the program reaches to the last variable in the input E,
; then the program will add it to the lst-result.
; GI: lst-of-all-ids = lst-result + all-ids(body-of-E)
;      where lst-result = lst-result + E if E is a variable
; -> lst-of-all-ids = lst-result + E
; -> lst-of-all-ids = lst-result 
;            
;
; Weak-enough?:
; In the first call the program make to the helper function, the id-so-far = `() -> an empty list  and body of E is still E.
; GI: lst-of-all-ids = lst-result + all-ids(body of E)
;      where lst-result = lst-result + E, if E is a variable
; -> lst-of-all-ids = `() + all-ids(E)
; -> lst-of-all-ids = all-ids(E)
;
; Preserved?
; Current call: Assume that the current call works, such that it works for the k amount of all-ids in the input E. So, the lst-result stored
;               all k ids.
; Next call: In the next call, we assumed that we have working k amount of all ids in the input E from the last call (current call,
;            we will need the cases because we process the different structures of lambda differenty.
;            1) if it is null, we return the empty lst.
;            
;            GI: lst-of-all-ids = E + lst-result + all-ids(None)
;            ->  lst-of-all-ids = lst-result
;
;           2) For a variable case, we add it to the lst-result
;               GI: lst-of-all-ids = E + lst-result + all-ids(None)
;            ->  lst-of-all-ids = lst-result + all-ids(None)
;            
;
;           3) If it is a lambda expression, we add the variable section to the lst-result


; Termination:  The program will terminate, if we have the empty list. And everytime we go through the body of the lambda function,
;               Therefore, assuming that the pre-condition holds, the program must terminate. 