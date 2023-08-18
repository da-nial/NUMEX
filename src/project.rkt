;; PL Project - Fall 2022
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

(require rackunit)

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var      (string)                       #:transparent)  ;; a variable, e.g., (var "foo")
(struct num      (int)                          #:transparent)  ;; a constant number, e.g., (num 17)
(struct plus     (e1 e2)                        #:transparent)  ;; add two expressions
(struct bool     (b)                            #:transparent)  ;; boolean
(struct minus    (e1 e2)                        #:transparent)  ;; subtract two expressions
(struct mult     (e1 e2)                        #:transparent)  ;; multiply two expressions
(struct div      (e1 e2)                        #:transparent)  ;; divide two expressions
(struct neg      (e1)                           #:transparent)  ;; negation
(struct andalso  (e1 e2)                        #:transparent)  ;; logical conjunction
(struct orelse   (e1 e2)                        #:transparent)  ;; logical disjunction
(struct cnd      (e1 e2 e3)                     #:transparent)  ;; condition
(struct iseq     (e1 e2)                        #:transparent)  ;; comparison
(struct ifnzero  (e1 e2 e3)                     #:transparent)  ;; if not zero condition
(struct ifleq    (e1 e2 e3 e4)                  #:transparent)  ;; less or equal condition


(struct lam      (nameopt formal body)          #:transparent)  ;; a recursive(?) 1-argument function
(struct tlam     (nameopt formal arg-type body) #:transparent)  ;; a typed argument, recursive(?) 1-argument function
(struct apply    (funexp actual)                #:transparent)  ;; function application
(struct with     (s e1 e2)                      #:transparent)  ;; let expression
(struct apair    (e1 e2)                        #:transparent)  ;; pair constructor
(struct 1st      (e)                            #:transparent)  ;; first part of a pair
(struct 2nd      (e)                            #:transparent)  ;; second part of a pair


(struct munit    ()                             #:transparent)  ;; unit value -- good for ending a list
(struct ismunit  (e)                            #:transparent)  ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e)                              #:transparent) ;; key holds corresponding value of s which is e
(struct record (k mr)                           #:transparent) ;; record holds several keys (nested, example: r (k r(k r(munit)))))
(struct value (s r)                             #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent) ;; a letrec expression for recursive definitions

;; Type structures
;; Primitive types are: "int", "bool" and "null"
(struct collection (type) #:transparent) ;; collection of a certain type, e.g., (collection "int")
(struct function (input-type output-type) #:transparent) ;; e.g. (function ("int" int")) means fn f "int" -> "int"

;; Problem 1

(define (racketlist->numexlist xs) (cond [(null? xs) (munit)]
                                         [else (apair (first xs) (racketlist->numexlist (rest xs)))]))

(define (numexlist->racketlist xs) (cond [(munit? xs) null]
                                         [else (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]))


;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(not (string? str)) (error ("str is not a string"))]
        [(not (list? env)) (error ("env in not a racket list"))]
        [(equal? str (car (first env)))  (cdr (first env))] ;evaluation
        [else (envlookup (rest env) str)] ;recursion
        )
  )

(define (reclookup rec target-key-str)  ;; recursively iterate record until finding target-key-str (otherwise return munit)
          (let ([key-str (key-s (record-k rec))]
                [key-val (key-e (record-k rec))] 
                [next-rec (record-mr rec)])
                  (cond [(equal? target-key-str key-str) key-val]
                        [(munit? (eval-exp next-rec)) (munit)]
                        [else (reclookup next-rec target-key-str)])))

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
         
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]
        
        ;; CHANGE add more cases here
        [(string? e) e]

        [(num? e)
         (if (integer? (num-int e)) e
             (error "NUMEX num applied to non-racket-integer"))]
        
        [(bool? e)
         (if (boolean? (bool-b e)) e
             (error "NUMEX bool applied to non-racket-boolean"))]

        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)(num? v2)) (num (- (num-int v1) (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)(num? v2)) (num (* (num-int v1) (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (equal? v2 (num 0)) (error "NUMEX division applied to zero")
               (if (and (num? v1)(num? v2)) (num (quotient (num-int v1) (num-int v2)))
                   (error "NUMEX divion applied to non-number"))
               )
           )]

        [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (cond [(num? v1) (num (- 0 (num-int v1)))]
                 [(bool? v1) (bool (not (bool-b v1)))]
                 [else (error "NUMEX negation applied to non-number and non-boolean")]))]
        
        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (if (bool? v1) (if (not (bool-b v1)) v1
                              (let ([v2 (eval-under-env (andalso-e2 e) env)])
                                   (if (bool? v2) v2
                                       (error "NUMEX conjunction applied to non-number"))))
               (error "NUMEX conjunction applied to non-number")))]
        
        [(orelse? e) 
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (if (bool? v1) (if (bool-b v1) v1
                                (let ([v2 (eval-under-env (orelse-e2 e) env)])
                                        (if (bool? v2) v2
                                             (error "NUMEX disjunction applied to non-number"))))
               (let ([v2 (eval-under-env (orelse-e2 e) env)])
                        (if (bool? v2) v2
                            (error "NUMEX disjunction applied to non-number")))))]

        [(cnd? e) 
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (if (bool? v1)
               (if (bool-b v1) (eval-under-env (cnd-e2 e) env)
                   (eval-under-env (cnd-e3 e) env))
               (error "NUMEX condition applied to non-boolean")))]

        [(iseq? e) 
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (cond [(and (bool? v1) (bool? v2)) (bool (equal? (bool-b v1) (bool-b v2)))]
                 [(and (num? v1) (num? v2)) (bool (equal? (num-int v1) (num-int v2)))]
                 [(and (bool v1) (num v2)) (bool #f)]
                 [(and (num v1) (bool v2)) (bool #f)]
                 [else (error "NUMEX equality is applied to something other than non-booleans or non-numbers")]))]

        [(ifnzero? e) 
         (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
           (if (num? v1)
               (if (not (zero? (num-int v1))) (eval-under-env (ifnzero-e2 e) env)
                   (eval-under-env (ifnzero-e3 e) env))
               (error "NUMEX ifnzero applied to non-number")))]

        [(ifleq? e) 
         (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (if (> (num-int v1) (num-int v2)) (eval-under-env (ifleq-e4 e) env)
                   (eval-under-env (ifleq-e3 e) env))
               (error "NUMEX ifleq applied to non-numbers")))]

        [(lam? e) 
         (closure env e)]

        [(apply? e)
         (let ([fun-closure (eval-under-env (apply-funexp e) env)])
           (cond[(closure? fun-closure) (let ([fun-def (closure-f fun-closure)])
                                          (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                            (cond[(lam? fun-def)(eval-under-env (lam-body fun-def) (cons (cons (lam-formal fun-def) eval-actual)
                                                                                                         (cons (cons (lam-nameopt fun-def) fun-closure) (closure-env fun-closure))))] 
                                                 [#t (error "closure function isn't lam")])))]

                [(lam? fun-closure) (let* ([lam-closure (eval-under-env fun-closure env)] 
                                           [lam-def (closure-f lam-closure)])
                                      (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                        (cond[(lam? lam-def)(eval-under-env (lam-body lam-def) (cons (cons (lam-formal lam-def) eval-actual)
                                                                                                     (cons (cons (lam-nameopt lam-def) lam-closure) (closure-env lam-closure))))] 
                                             [#t (error "closure function isn't lam")])))]
                [else (error (format "NUMEX lam apply invalid"))]))]
        
        [(with? e) 
         (let ([v1 (eval-under-env (with-e1 e) env)])
           ; env -> (s, eval(e1)) + env
           (if (or (string? (with-s e)) (munit? (with-s e)))
               (let ([expanded_env (cons (cons (with-s e) v1) env)])
                  (eval-under-env (with-e2 e) expanded_env))
               (error "NUMEX with applied to non-string")))]

        [(apair? e) 
         ; apair e1 e2 -> apair eval(e1) (e2)
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]

        [(1st? e) 
         ; if eval(e) = apair e1 e2 -> e1
         (let ([v1 (eval-under-env (1st-e e) env)])
           (if (apair? v1) (apair-e1 v1)
               (error "NUMEX 1st applied to non-apair")))]

        [(2nd? e) 
        ; if eval(e) = apair e1 e2 -> e2
         (let ([v1 (eval-under-env (2nd-e e) env)])
           (if (apair? v1) (apair-e2 v1)
               (error "NUMEX 2nd applied to non-apair")))]

        [(munit? e) (munit)] 

        [(ismunit? e)
          (bool (munit? (eval-under-env (ismunit-e e) env)))]

        [(closure? e) e] 

        [(key? e)
         (let ([ex (eval-under-env (key-e e) env)])
           (if (string? (key-s e)) e
               (error (format "key s e: s is not a string, s: ~v" (key-s e)))))]

        [(record? e)
         ; each record has two params, k (a key) and mr (another record or otherwise munit)
         ; record k mr -> record eval(k) eval(mr)
         (let ([k (eval-under-env (record-k e) env)]
               [mr (eval-under-env (record-mr e) env)])
           (if (key? k) (if (or (munit? (eval-exp mr)) (record? mr)) (record k mr)
                            (error (format "record k mr: mr is neither a record or munit, mr: %v" (record-mr e))))
               (error (format "record k mr: k is not a key, k: ~v" (record-k e)))))]

        [(value? e)
         (let ([rec (eval-under-env (value-r e) env)])
           (cond [(and (string? (value-s e)) (record? rec))
                 (reclookup rec (value-s e))]
                [else (error "NUMEX value applied to non-string")]))]

        [(letrec? e)
         (cond [(and (string? (letrec-s1 e))
                     (string? (letrec-s2 e))
                     (string? (letrec-s3 e))
                     (string? (letrec-s4 e)))
                (eval-under-env (letrec-e5 e) (append (list (cons (letrec-s1 e) (letrec-e1 e))
                                                            (cons (letrec-s2 e) (letrec-e2 e))
                                                            (cons (letrec-s3 e) (letrec-e3 e))
                                                            (cons (letrec-s4 e) (letrec-e4 e))) env))]
               [else (error "NUMEX letrec applied to non-string s")])]
        
        [#t (error (format "bad NUMEX expression: ~v" e))]
        ))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))

;; Problem 3
;; Complete more cases for other kinds of NUMEX expressions.
;; We will test infer-under-env by calling its helper function, infer-exp.

(define bool_t "bool")
(define int_t "int")
(define null_t "null")

(define (infer-under-env e env)
  (cond [(var? e)
         (infer-under-env (envlookup env (var-string e)) env)]

        [(munit? e) null_t]

        [(num? e)
         (if (integer? (num-int e)) int_t
           (error "NUMEX TYPE ERROR: num should be a constant number"))]

        [(bool? e)
         (if (boolean? (bool-b e)) bool_t
             (error "NUMEX TYPE ERROR: bool should be #t or #f"))]

        [(string? e) e]

        [(plus? e)
         (let ([t1 (infer-under-env (plus-e1 e) env)]
               [t2 (infer-under-env (plus-e2 e) env)])
           (if (and (equal? int_t t1) (equal? int_t t2)) int_t
               (error "NUMEX TYPE ERROR: aithmetic operation applied to non-integer")))]

        [(minus? e)
         (let ([t1 (infer-under-env (minus-e1 e) env)]
               [t2 (infer-under-env (minus-e2 e) env)])
           (if (and (equal? int_t t1) (equal? int_t t2)) int_t
               (error "NUMEX TYPE ERROR: aithmetic operation applied to non-integer")))]

        [(mult? e)
         (let ([t1 (infer-under-env (mult-e1 e) env)]
               [t2 (infer-under-env (mult-e2 e) env)])
           (if (and (equal? int_t t1) (equal? int_t t2)) int_t
               (error "NUMEX TYPE ERROR: aithmetic operation applied to non-integer")))]

        [(div? e)
         (let ([t1 (infer-under-env (div-e1 e) env)]
               [t2 (infer-under-env (div-e2 e) env)])
           (if (and (equal? int_t t1) (equal? int_t t2)) int_t
               (error "NUMEX TYPE ERROR: aithmetic operation applied to non-integer")))]
        
        [(andalso? e)
         (let ([t1 (infer-under-env (andalso-e1 e) env)]
               [t2 (infer-under-env (andalso-e2 e) env)])
           (if (and (equal? bool_t t1) (equal? bool_t t2)) bool_t
               (error "NUMEX TYPE ERROR: logical operation applied to non-integer")))]

        [(orelse? e)
         (let ([t1 (infer-under-env (orelse-e1 e) env)]
               [t2 (infer-under-env (orelse-e2 e) env)])
           (if (and (equal? bool_t t1) (equal? bool_t t2)) bool_t
               (error "NUMEX TYPE ERROR: logical operation applied to non-integer")))]

        [(neg? e)
        (let ([t (infer-under-env (neg-e1 e) env)])
           (if (equal? null_t t) (error "NUMEX TYPE ERROR: neg applied to null")
              (infer-under-env (neg-e1 e) env)))]

        [(cnd? e)
         (let
             ([t1 (infer-under-env (cnd-e1 e) env)]
              [t2 (infer-under-env (cnd-e2 e) env)]
              [t3 (infer-under-env (cnd-e3 e) env)])
           (if (equal? bool_t t1)
               (if (equal? t2 t3) t2
                   (error "NUMEX TYPE ERROR: cnd e1 e2 e3: e2 and e3 types do not match."))
               (error "NUMEX TYPE ERROR: cnd e1 e2 e3: e1 type is not bool.")))]

        [(iseq? e)
         (let
             ([t1 (infer-under-env (iseq-e1 e) env)]
              [t2 (infer-under-env (iseq-e2 e) env)])
           (if (equal? t1 t2) bool_t
               (error "NUMEX TYPE ERROR: iseq e1 e2: e1 and e2 types do not match."))
           )]
        
        [(with? e)
         (if (string? (with-s e))
             (let ([t1 (infer-under-env (with-e1 e) env)])
               (infer-under-env (with-e2 e) (cons (cons (with-s e) t1) env)))
             (error "NUMEX TYPE ERROR: with s e1 e2: s is not a string"))]

        [(tlam? e)
         (function (tlam-arg-type e) (infer-under-env (tlam-body e) (cons (cons (tlam-formal e) (tlam-arg-type e)) env)))]

        [(apply? e)
         (let ([t1 (infer-under-env (apply-funexp e) env)]
               [t2 (infer-under-env (apply-actual e) env)])
           (if (function? t1)
               (if (equal? t2 (function-input-type t1)) (function-output-type t1)
                   (error "arugment should be the same type as input type"))
               (error "first argument should be a function")))]

        [(apair? e)
         (let ([t1 (infer-under-env (apair-e1 e) env)]
               [t2 (infer-under-env (apair-e2 e) env)])
           (if (equal? null_t t2) (collection t1)
               (if (collection? t2)
                   (if (equal? t1 (collection-type t2)) (collection t1)
                       (error "NUMEX TYPE ERROR: apair e1 e2: type of (e1) and (elements of e2) do not match"))
                   (error "NUMEX TYPE ERROR: apair e1 e2: type of e2 is neither null nor collection"))))]
                   
        [(1st? e)
         (let ([t (infer-under-env (1st-e e) env)])
           (if (collection? t) (collection-type t)
               (error "NUMEX TYPE ERROR: 1st e: e is not of type collection")))]

        [(2nd? e)
         (let ([t (infer-under-env (2nd-e e) env)])
           (if (collection? t) t
               (error "NUMEX TYPE ERROR: 2nd e: e is not of type collection")))]
      
        [(ismunit? e)
         (let ([t (infer-under-env (ismunit-e e) env)])
           (if (or (collection? t) (equal? null_t t)) bool_t
               (error "NUMEX TYPE ERROR: ismunit e: type of e is neither collection nor null")))]
        
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (infer-exp e)
  (infer-under-env e null))

;; Problem 4

(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3))

(define (with* bs e2)
  (cond [(ismunit? bs) e2]
        [(null? bs) e2]
        [(with (car (first bs)) (cdr (first bs)) (with* (rest bs) e2))]))

(define (ifneq e1 e2 e3 e4)
  (with "_x" e1
        (with "_y" e2
              (cnd (iseq (var "_x") (var "_y")) e4 e3))
  )
  )

;; Problem 5
(define numex-filter (lam "map_generator" "f"
                           (lam "map" "xs"
                                (ifmunit (var "xs")
                                         (munit)
                                         (ifnzero (apply (var "f") (1st (var "xs")))
                                                      (apair (apply (var "f") (1st (var "xs"))) (apply (var "map") (2nd (var "xs"))))
                                                      (apply (var "map") (2nd (var "xs")))
                                                      )

                                         )
                                )
                           )
)

(define numex-all-gt
  (with "filter" numex-filter
        ; notice filter is now in NUMEX scope
        (lam null "i" ; anonymous function
             (lam null "list"
                  (apply
                   (apply (var "filter")
                          (lam "gt" "num"
                              (ifleq (var "num") (var "i")
                                      (num 0)
                                      (var "num")
                                      )
                              )
                          )
                   (var "list")
                   )
                  )
             )
        ))

;; Problem 6
(define type-error-but-evaluates-ok (orelse (bool #t) (num 1)))
; (eval-exp type-error-but-evaluates-ok)
; (infer-exp type-error-but-evaluates-ok)

(define type-ok-but-evaluates-error  (neg "randomString"))
; (infer-exp type-ok-but-evaluates-error)
; (eval-exp type-ok-but-evaluates-error)

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e)
  (cond[(var? e) e]
       ;;
       [(lam? e) (fun-challenge (lam-nameopt e) (lam-formal e) (compute-free-vars (lam-body e)) (cfv e))]
       [(with? e) (with (with-s e) (compute-free-vars (with-e1 e)) (compute-free-vars (with-e2 e)))]
       [(apply? e) (apply (compute-free-vars (apply-funexp e)) (compute-free-vars (apply-actual e)))]

       ;; Pairs 
       [(apair? e) (apair (compute-free-vars (apair-e1 e)) (compute-free-vars (apair-e2 e)))]
       [(1st? e) (1st (compute-free-vars (1st-e e)))]
       [(2nd? e) (2nd (compute-free-vars (2nd-e e)))]
       
       ;; Conditions 
       [(cnd? e) (cnd (compute-free-vars (cnd-e1 e)) (compute-free-vars (cnd-e2 e)) (compute-free-vars (cnd-e3 e)))]
       [(iseq? e) (iseq (compute-free-vars (iseq-e1 e)) (compute-free-vars (iseq-e2 e)))]
       [(ifnzero? e) (ifnzero (compute-free-vars (ifnzero-e1 e)) (compute-free-vars (ifnzero-e2 e)) (compute-free-vars (ifnzero-e3 e)))]
       [(ifleq? e) (ifleq (compute-free-vars (ifleq-e1 e)) (compute-free-vars (ifleq-e2 e)) (compute-free-vars (ifleq-e3 e)) (compute-free-vars (ifleq-e4 e)))]
       [(ismunit? e) (ismunit (compute-free-vars (ismunit-e e)))]
       
       ;; Logical
       [(andalso? e) (andalso (compute-free-vars (andalso-e1 e)) (compute-free-vars (andalso-e2 e)))]
       [(orelse? e) (orelse (compute-free-vars (orelse-e1 e)) (compute-free-vars (orelse-e2 e)))]
       
       ;; Arithmetic
       [(plus? e) (plus (compute-free-vars (plus-e1 e)) (compute-free-vars (plus-e2 e)))]
       [(minus? e) (minus (compute-free-vars (minus-e1 e)) (compute-free-vars (minus-e2 e)))]
       [(mult? e) (mult (compute-free-vars (mult-e1 e)) (compute-free-vars (mult-e2 e)))]
       [(div? e) (div (compute-free-vars (div-e1 e)) (compute-free-vars (div-e2 e)))]
       [(neg? e) (neg (compute-free-vars (neg-e1 e)))]
       [(num? e) e]
       [(bool? e) e]
       [(closure? e) e]
       [(string? e) e]
       [(munit? e) e]
       
       [#t (error "NUMEX Compute free vars wrong type" e)]
       )
  )

(define (cfv e)
  (cond[(var? e)  ;; Variables
        (set (var-string e))]
      
       ;; Other 
       [(lam? e) (set-remove (set-remove (cfv (lam-body e)) (lam-nameopt e)) (lam-formal e))]  ; remove function name and its argument name from its body free vars     
       [(with? e) (set-union (set-remove (cfv (with-e2 e)) (with-s e)) (cfv (with-e1 e)) )]    ; for with s e1 e2: return cfv(e2) + cfv(e1) - s
       [(apply? e) (set-union (cfv (apply-funexp e))(cfv (apply-actual e)))]                   ;
       
       ;; Pairs 
       [(apair? e) (set-union (cfv (apair-e1 e)) (cfv (apair-e2 e)))]
       [(1st? e) (cfv (1st-e e))]
       [(2nd? e) (cfv (2nd-e e))]
      
       ;; Conditions 
       [(cnd? e) (set-union (cfv (cnd-e1 e)) (cfv (cnd-e2 e)) (cfv (cnd-e3 e)))]
       [(iseq? e) (set-union (cfv (iseq-e1 e)) (cfv (iseq-e2 e)))]
       [(ifnzero? e) (set-union (cfv (ifnzero-e1 e)) (cfv (ifnzero-e2 e)) (cfv (ifnzero-e3 e)))]
       [(ifleq? e) (set-union (cfv (ifleq-e1 e)) (cfv (ifleq-e2 e)) (cfv (ifleq-e3 e)) (cfv (ifleq-e4 e)))]
       [(ismunit? e) (cfv (ismunit-e e))]

       ;; Logical
       [(andalso? e) (set-union (cfv (andalso-e1 e)) (cfv (andalso-e2 e)))]
       [(orelse? e) (set-union (cfv (orelse-e1 e)) (cfv (orelse-e2 e)))]

       ;; Arithmetic
       [(plus? e) (set-union (cfv (plus-e1 e)) (cfv (plus-e2 e)))]
       [(minus? e) (set-union (cfv (minus-e1 e)) (cfv (minus-e2 e)))]
       [(mult? e) (set-union (cfv (mult-e1 e)) (cfv (mult-e2 e)))]
       [(div? e) (set-union (cfv (div-e1 e)) (cfv (div-e2 e)))]
       [(neg? e) (cfv (neg-e1 e))]
       [(num? e) (set)]
       [(bool? e) (set)]
       [(closure? e) (set)]
       [(munit? e) (set)]
       [(string? e) (set)]
       [#t (error (format "bad NUMEX expression: ~v" e))]
       )
  )

(define (exclude_non_free_vars env free)
  (cond[(null? env) null]
       [(set-member? free (car (car env))) (cons (car env) (exclude_non_free_vars (cdr env) (set-remove free (car (car env)))))]
       [#t (exclude_non_free_vars (cdr env) free)]
       )
  )

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env)
  (cond [(var? e)  ;; Variables
           (envlookup env (var-string e))]
      
        ;;
        [(fun-challenge? e)
         (if (and (or (string? (fun-challenge-nameopt e)) (null? (fun-challenge-nameopt e))) (string? (fun-challenge-formal e)))
             (closure (exclude_non_free_vars env (fun-challenge-freevars e)) e)
             (error "NUMEX function name and parameter name must be string"))]
        
        [(with? e)
         (eval-under-env-c (with-e2 e) (cons (cons (with-s e)(eval-under-env-c (with-e1 e) env)) env))]

        [(apply? e)
         (let ([v1 (eval-under-env-c (apply-funexp e) env)]
               [v2 (eval-under-env-c (apply-actual e) env)])
           (if (closure? v1)
               (if (null? (fun-challenge-nameopt (closure-f v1)))
                   (eval-under-env-c (fun-challenge-body (closure-f v1)) (cons (cons (fun-challenge-formal (closure-f v1)) v2) (closure-env v1)))
                   (eval-under-env-c (fun-challenge-body (closure-f v1)) (cons (cons (fun-challenge-nameopt (closure-f v1)) v1) (cons (cons (fun-challenge-formal (closure-f v1)) v2) (closure-env v1)))))
               (error  "NUMUX apply applied to non-closure" v1 (apply-funexp e))
               ))]


        ;; Pairs 
        [(apair? e)
         (let ([v1 (eval-under-env-c (apair-e1 e) env)]
               [v2 (eval-under-env-c (apair-e2 e) env)])
           (apair v1 v2))]

        [(1st? e)
         (let ([v1 (eval-under-env-c (1st-e e) env)])
           (if (apair? v1)
               (apair-e1 v1)
               (error "NUMUX 1st applied to non-apair")))]

        [(2nd? e)
         (let ([v1 (eval-under-env-c (2nd-e e) env)])
           (if (apair? v1)
               (apair-e2 v1)
               (error "NUMUX 1st applied to non-apair")))]

       
        ;; Conditions 
        [(cnd? e)
         (let ([v1 (eval-under-env-c (cnd-e1 e) env)])
           (if (bool? v1)
               (if (bool-b v1)
                   (eval-under-env-c (cnd-e2 e) env)
                   (eval-under-env-c (cnd-e3 e) env)
                   )
               (error "NUMUX cnd guard applied to non-boolean"))
           )]

        [(iseq? e)
         (let ([v1 (eval-under-env-c (iseq-e1 e) env)]
               [v2 (eval-under-env-c (iseq-e2 e) env)])
           (cond
             [(and (num? v1)(num? v2))
              (bool (equal? (num-int v1) (num-int v2)))]
             [(and (bool? v1)(bool? v2))
              (bool (equal? (bool-b v1)(bool-b v2)))]
             [#t (bool #f)]
             ))]

        [(ifnzero? e)
         (let ([v1 (eval-under-env-c (ifnzero-e1 e) env)])
           (if (num? v1)
               (if (equal? (num-int v1) 0)
                   (eval-under-env-c (ifnzero-e3 e) env)
                   (eval-under-env-c (ifnzero-e2 e) env))
               (error "NUMUX ifnzero applied to a non-number")
               ))]

        [(ifleq? e)
         (let ([v1 (eval-under-env-c (ifleq-e1 e) env)]
               [v2 (eval-under-env-c (ifleq-e2 e) env)])
           (if (and
                (num? v2)
                (num? v1))
               (if (<= (num-int v1)(num-int v2))
                   (eval-under-env-c (ifleq-e3 e) env)
                   (eval-under-env-c (ifleq-e4 e) env))
               (error "NUMUX ifleq applied to a non-number")
               ))]

        [(ismunit? e)
         (let ([v1 (eval-under-env-c (ismunit-e e) env)])
           (bool (munit? v1))
           )]
        
        ;; Logical
        [(andalso? e) 
         (let ([v1 (eval-under-env-c (andalso-e1 e) env)])
           (let ([v3 (cond[(bool? v1) v1]
                          [(num? v1) (if (equal? (num-int v1) 0) (bool #f) (bool #t))]
                          [#t error "NUMEX and-also applied to non-number or non-boolean"])])
             (if (and (bool? v3) (equal? (bool-b v3) #f))
                 (bool #f)
                 (let ([v2 (eval-under-env-c (andalso-e2 e) env)])
                   (let ([v4 (cond[(bool? v2) v2]
                                  [(num? v2) (if (equal? (num-int v2) 0) (bool #f) (bool #t))]
                                  [#t error "NUMEX and-also applied to non-number or non-boolean"])])
                     v4
                     )))
             ))]
        
        [(orelse? e)
         (let ([v1 (eval-under-env-c (orelse-e1 e) env)])
           (let ([v3 (cond[(bool? v1) v1]
                          [(num? v1) (if (equal? (num-int v1) 0) (bool #f) (bool #t))]
                          [#t error "NUMEX orelse applied to non-number or non-boolean"])])
             (if (and (bool? v3) (equal? (bool-b v3) #t))
                 (bool #t)
                 (let ([v2 (eval-under-env-c (orelse-e2 e) env)])
                   (let ([v4 (cond[(bool? v2) v2]
                                  [(num? v2) (if (equal? (num-int v2) 0) (bool #f) (bool #t))]
                                  [#t error "NUMEX orelse applied to non-number or non-boolean"])])
                     v4
                     )))
             ))]
        
        ;; Arithmetic
        [(plus? e) 
         (let ([v1 (eval-under-env-c (plus-e1 e) env)]
               [v2 (eval-under-env-c (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]

        [(minus? e) 
         (let ([v1 (eval-under-env-c (minus-e1 e) env)]
               [v2 (eval-under-env-c (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(mult? e) 
         (let ([v1 (eval-under-env-c (mult-e1 e) env)]
               [v2 (eval-under-env-c (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiply applied to non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env-c (div-e1 e) env)]
               [v2 (eval-under-env-c (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (equal? (num-int v2) 0)
                   (error "NUMEX division applied to Zero" v2)
                   (num (quotient (num-int v1) 
                                  (num-int v2))))
               (error "NUMEX division applied to non-number")))]

        [(neg? e) 
         (let ([v1 (eval-under-env-c (neg-e1 e) env)])
           (if (num? v1)
               (num (- (num-int v1)))
               (if (bool? v1)
                   (bool (if (bool-b v1) #f #t))
                   (error "NUMEX Nagation applied to non-number or non-boolean"))
               ))]
        
        [(num? e) (if (integer? (num-int e)) e
                      (error "NUMEX num applied to non-integer"))]

        ; [(num? e)
        ;  (let ([v1 (eval-under-env-c (num-int e) env)])
        ;    (if (integer? v1) (num v1) (error "NUMEX num applied to non-integer")))]

        [(bool? e)
         (let ([v1 (eval-under-env-c (bool-b e) env)])
           (if (boolean? v1) (bool v1) (error "NUMEX bool appllied to non-boolean")))]

        [(closure? e) e]
        [(number? e)  e]
        [(boolean? e) e]
        [(string? e) e]
        [(munit? e) e]
        [#t (error (format "bad NUMEX expression: ~v" e))])
  )

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))


























(define (racket_exp n)(
  cond [(= n 0) 1]
  [(> n 0) (* 2 (racket_exp (- n 1)))]
  )
)

(define (exp n)(
  eval-exp (apply (lam "exp" "x"
                       (ifleq (var "x") (num 1)
                              (num 1)
                              (mult (num 2) (apply (var "exp") (minus (var "x") (num 1))))
                              )
                       ) (num n)
                  )
           )
)

(exp 5)




































