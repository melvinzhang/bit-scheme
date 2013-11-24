;; eiod.scm: eval-in-one-define
;; $Id: eiod.scm,v 1.17 2005/03/26 19:57:44 al Exp $

;; A minimal implementation of r5rs eval, null-environment, and
;; scheme-report-environment.  (And SRFI-46 extensions, too.)

;; Copyright 2002, 2004, 2005 Al Petrofsky <al@petrofsky.org>

;; You may redistribute and/or modify this software under the terms of
;; the GNU General Public License as published by the Free Software
;; Foundation (fsf.org); either version 2, or (at your option) any
;; later version.

;; Feel free to ask me for different licensing terms. 

;; DISCLAIMER: 

;; This is only intended as a demonstration of the minimum
;; implementation effort required for an r5rs eval.  It serves as a
;; simple, working example of one way to implement the r5rs macro
;; system (and SRFI-46) .  Among the reasons that it is ill-suited for
;; production use is the complete lack of error-checking.

;; DATA STRUCTURES:

;; An environment is a procedure that accepts any identifier and
;; returns a denotation.  The denotation of an unbound identifier is
;; its name (as a symbol).  A bound identifier's denotation is its
;; binding, which is a list of the current value, the binding's type
;; (keyword or variable), and the identifier's name (needed by quote).

;; identifier:       [symbol | thunk]
;; denotation:       [symbol | binding]
;; binding:          [variable-binding | keyword-binding]
;; variable-binding: (value        #f symbol)
;; keyword-binding:  (special-form #t symbol)
;; special-form:     [builtin | transformer]

;; A value is any arbitrary scheme value.  Special forms are either a
;; symbol naming a builtin, or a transformer procedure that takes two
;; arguments: a macro use and the environment of the macro use.

;; An explicit-renaming low-level macro facility is supported, upon
;; which syntax-rules is implemented.  When a syntax-rules template
;; containing a literal identifier is transcribed, the output will
;; contain a fresh identifier, which is an eq?-unique thunk that when
;; invoked returns the old identifier's denotation in the environment
;; of the macro's definition.  When one of these "renamed" identifiers
;; is looked up in an environment that has no binding for it, the
;; thunk is invoked and the old denotation is returned.  (The thunk
;; actually returns the old denotation wrapped inside a unique pair,
;; which is immediately unwrapped.  This is necessary to ensure that
;; different rename thunks of the same denotation do not compare eq?.)

;; This environment and denotation model is similar to the one
;; described in the 1991 paper "Macros that Work" by Clinger and Rees.

;; The base environment contains eight keyword bindings and two
;; variable bindings:
;;   lambda, set!, and begin are as in the standard.
;;   q is like quote, but it does not handle pairs or vectors.
;;   def is like define, but it does not handle the (f . args) format.
;;   define-syntax makes internal syntax definitions.
;;   (get-env) returns the local environment.
;;   (syntax x) is like quote, but does not convert identifiers to symbols.
;;   The id? procedure is a predicate for identifiers.
;;   The new-id procedure takes a denotation and returns a fresh identifier.


;; Quote-and-evaluate captures all the code into the list eiod-source
;; so that we can have fun feeding eval to itself, as in
;; ((eval `(let () ,@eiod-source repl) (scheme-report-environment 5))).
;; [Note: using (and even starting) a doubly evaled repl will be *very* slow.]
(define-syntax quote-and-evaluate
  (syntax-rules () ((quote-and-evaluate var . x) (begin (define var 'x) . x))))

;; The matching close parenthesis is at the end of the file.
(quote-and-evaluate eiod-source

(define (eval sexp env)
  (define (new-id den)    (define p (list den)) (lambda () p))
  (define (old-den id)    (car (id)))
  (define (id? x)         (or (symbol? x) (procedure? x)))
  (define (id->sym id)    (if (symbol? id) id (den->sym (old-den id))))
  (define (den->sym den)  (if (symbol? den) den (get-sym den)))

  (define (empty-env id)          (if (symbol? id) id (old-den id)))
  (define (extend env id binding) (lambda (i) (if (eq? id i) binding (env i))))
  (define (add-var var val env)   (extend env var (list val #f (id->sym var))))
  (define (add-key key val env)   (extend env key (list val #t (id->sym key))))

  (define (get-val  binding)      (car binding))
  (define (special? binding)      (cadr binding))
  (define (get-sym  binding)      (caddr binding))
  (define (set-val! binding val)  (set-car! binding val))

  (define (make-builtins-env)
    (do ((specials '(lambda set! begin q def define-syntax syntax get-env)
		   (cdr specials))
	 (env empty-env (add-key (car specials) (car specials) env)))
	((null? specials) (add-var 'new-id new-id (add-var 'id? id? env)))))

  (define (eval sexp env)
    (let eval-here ((sexp sexp))
      (cond ((id? sexp) (get-val (env sexp)))
	    ((not (pair? sexp)) sexp)
	    (else (let ((head (car sexp)) (tail (cdr sexp)))
		    (let ((head-binding (and (id? head) (env head))))
		      (if (and head-binding (special? head-binding))
			  (let ((special (get-val head-binding)))
			    (case special
			      ((get-env) env)
			      ((syntax) (car tail))
			      ((lambda) (eval-lambda tail env))
			      ((begin) (eval-seq tail env))
			      ((set!) (set-val! (env (car tail))
						(eval-here (cadr tail))))
			      ((q) (let ((x (car tail)))
				     (if (id? x) (id->sym x) x)))
			      (else (eval-here (special sexp env)))))
			  (apply (eval-here head)
				 (map1 eval-here tail)))))))))

  ;; Don't use standard map because it might not be continuationally correct.
  (define (map1 f l)
    (if (null? l)
	'()
	(cons (f (car l)) (map1 f (cdr l)))))

  (define (eval-seq tail env)
    ;; Don't use for-each because we must tail-call the last expression.
    (do ((sexps tail (cdr sexps)))
	((null? (cdr sexps)) (eval (car sexps) env))
      (eval (car sexps) env)))

  (define (eval-lambda tail env)
    (lambda args
      (define ienv (do ((args args (cdr args))
			(vars (car tail) (cdr vars))
			(ienv env (add-var (car vars) (car args) ienv)))
		       ((not (pair? vars))
			(if (null? vars) ienv (add-var vars args ienv)))))
      (let loop ((ienv ienv) (ids '()) (inits '()) (body (cdr tail)))
	(let ((first (car body)) (rest (cdr body)))
	  (let* ((head (and (pair? first) (car first)))
		 (binding (and (id? head) (ienv head)))
		 (special (and binding (special? binding) (get-val binding))))
	    (if (procedure? special)
		(loop ienv ids inits (cons (special first ienv) rest))
		(case special
		  ((begin) (loop ienv ids inits (append (cdr first) rest)))
		  ((def define-syntax)
		   (let ((id (cadr first)) (init (caddr first)))
		     (let* ((adder (if (eq? special 'def) add-var add-key))
			    (ienv (adder id 'undefined ienv)))
		       (loop ienv (cons id ids) (cons init inits) rest))))
		  (else (let ((ieval (lambda (init) (eval init ienv))))
			  (for-each set-val! (map ienv ids) (map1 ieval inits))
			  (eval-seq body ienv))))))))))

  ;; We make a copy of the initial input to ensure that subsequent
  ;; mutation of it does not affect eval's result. [1]
  (eval (let copy ((x sexp))
	  (cond ((string? x) (string-copy x))
		((pair? x) (cons (copy (car x)) (copy (cdr x))))
		((vector? x) (list->vector (copy (vector->list x))))
		(else x)))
	(or env (make-builtins-env))))


(define null-environment
  (let ()
    ;; Syntax-rules is implemented as a macro that expands into a call
    ;; to the syntax-rules* procedure, which returns a transformer
    ;; procedure.  The arguments to syntax-rules* are the arguments to
    ;; syntax-rules plus the current environment, which is captured
    ;; with get-env.  Syntax-rules** is called once with some basics
    ;; from the base environment.  It creates and returns
    ;; syntax-rules*.
    (define (syntax-rules** id? new-id denotation-of-default-ellipsis)
      (define (syntax-rules* mac-env ellipsis pat-literals rules)
        (define (pat-literal? id)     (memq id pat-literals))
	(define (not-pat-literal? id) (not (pat-literal? id)))
	(define (ellipsis-pair? x)    (and (pair? x) (ellipsis? (car x))))
	(define (ellipsis? x)
	  (if ellipsis
	      (eq? x ellipsis)
	      (and (id? x)
		   (eq? (mac-env x) denotation-of-default-ellipsis))))

	;; List-ids returns a list of the non-ellipsis ids in a
	;; pattern or template for which (pred? id) is true.  If
	;; include-scalars is false, we only include ids that are
	;; within the scope of at least one ellipsis.
	(define (list-ids x include-scalars pred?)
	  (let collect ((x x) (inc include-scalars) (l '()))
	    (cond ((id? x) (if (and inc (pred? x)) (cons x l) l))
		  ((vector? x) (collect (vector->list x) inc l))
		  ((pair? x)
		   (if (ellipsis-pair? (cdr x))
		       (collect (car x) #t (collect (cddr x) inc l))
		       (collect (car x) inc (collect (cdr x) inc l))))
		  (else l))))
    
	;; Returns #f or an alist mapping each pattern var to a part of
	;; the input.  Ellipsis vars are mapped to lists of parts (or
	;; lists of lists ...).
	(define (match-pattern pat use use-env)
	  (call-with-current-continuation
	    (lambda (return)
	      (define (fail) (return #f))
	      (let match ((pat (cdr pat)) (sexp (cdr use)) (bindings '()))
		(define (continue-if condition) (if condition bindings (fail)))
		(cond
		 ((id? pat)
		  (if (pat-literal? pat)
		      (continue-if (and (id? sexp)
					(eq? (use-env sexp) (mac-env pat))))
		      (cons (cons pat sexp) bindings)))
		 ((vector? pat)
		  (or (vector? sexp) (fail))
		  (match (vector->list pat) (vector->list sexp) bindings))
		 ((not (pair? pat)) (continue-if (equal? pat sexp)))
		 ((ellipsis-pair? (cdr pat))
		  (let* ((tail-len (length (cddr pat)))
			 (sexp-len (if (list? sexp) (length sexp) (fail)))
			 (seq-len (- sexp-len tail-len))
			 (sexp-tail (begin (if (negative? seq-len) (fail))
					   (list-tail sexp seq-len)))
			 (seq (reverse (list-tail (reverse sexp) tail-len)))
			 (vars (list-ids (car pat) #t not-pat-literal?)))
		    (define (match1 sexp) (map cdr (match (car pat) sexp '())))
		    (append (apply map list vars (map match1 seq))
			    (match (cddr pat) sexp-tail bindings))))
		 ((pair? sexp) (match (car pat) (car sexp)
				      (match (cdr pat) (cdr sexp) bindings)))
		 (else (fail)))))))

	(define (expand-template pat tmpl top-bindings)
	  ;; New-literals is an alist mapping each literal id in the
	  ;; template to a fresh id for inserting into the output.  It
	  ;; might have duplicate entries mapping an id to two different
	  ;; fresh ids, but that's okay because when we go to retrieve a
	  ;; fresh id, assq will always retrieve the first one.
	  (define new-literals
	    (map (lambda (id) (cons id (new-id (mac-env id))))
		 (list-ids tmpl #t (lambda (id)
				     (not (assq id top-bindings))))))
	  (define ellipsis-vars (list-ids (cdr pat) #f not-pat-literal?))
	  (define (list-ellipsis-vars subtmpl)
	    (list-ids subtmpl #t (lambda (id) (memq id ellipsis-vars))))
	  (let expand ((tmpl tmpl) (bindings top-bindings))
	    (let expand-part ((tmpl tmpl))
	      (cond
	       ((id? tmpl) (cdr (or (assq tmpl bindings)
				    (assq tmpl top-bindings)
				    (assq tmpl new-literals))))
	       ((vector? tmpl)
		(list->vector (expand-part (vector->list tmpl))))
	       ((pair? tmpl)
		(if (ellipsis-pair? (cdr tmpl))
		    (let ((vars-to-iterate (list-ellipsis-vars (car tmpl))))
		      (define (lookup var) (cdr (assq var bindings)))
		      (define (expand-using-vals . vals)
			(expand (car tmpl) (map cons vars-to-iterate vals)))
		      (let ((val-lists (map lookup vars-to-iterate)))
			(append (apply map expand-using-vals val-lists)
				(expand-part (cddr tmpl)))))
		    (cons (expand-part (car tmpl)) (expand-part (cdr tmpl)))))
	       (else tmpl)))))

	(lambda (use use-env)
	  (let loop ((rules rules))
	    (let* ((rule (car rules)) (pat (car rule)) (tmpl (cadr rule)))
	      (cond ((match-pattern pat use use-env) =>
		     (lambda (bindings) (expand-template pat tmpl bindings)))
		    (else (loop (cdr rules))))))))
      syntax-rules*)
    (define macro-defs
      '((define-syntax quote
	  (syntax-rules ()
	    ('(x . y) (cons 'x 'y))
	    ('#(x ...) (list->vector '(x ...)))
	    ('x (q x))))
	(define-syntax quasiquote
	  (syntax-rules (unquote unquote-splicing quasiquote)
	    (`,x x)
	    (`(,@x . y) (append x `y))
	    ((_ `x . d) (cons 'quasiquote       (quasiquote (x)   d)))
	    ((_ ,x   d) (cons 'unquote          (quasiquote (x) . d)))
	    ((_ ,@x  d) (cons 'unquote-splicing (quasiquote (x) . d)))
	    ((_ (x . y) . d)
	     (cons (quasiquote x . d) (quasiquote y . d)))
	    ((_ #(x ...) . d)
	     (list->vector (quasiquote (x ...) . d)))
	    ((_ x . d) 'x)))
	(define-syntax do
	  (syntax-rules ()
	    ((_ ((var init . step) ...)
		ending
		expr ...)
	     (let loop ((var init) ...)
	       (cond ending (else expr ... (loop (begin var . step) ...)))))))
	(define-syntax letrec
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     (let () (def var init) ... (let () . body)))))
	(define-syntax letrec-syntax
	  (syntax-rules ()
	    ((_ ((key trans) ...) . body)
	     (let () (define-syntax key trans) ... (let () . body)))))
	(define-syntax let-syntax
	  (syntax-rules ()
	    ((_ () . body) (let () . body))
	    ((_ ((key trans) . bindings) . body)
	     (letrec-syntax ((temp trans))
	       (let-syntax bindings (letrec-syntax ((key temp)) . body))))))
	(define-syntax let*
	  (syntax-rules ()
	    ((_ () . body) (let () . body))
	    ((_ (first . more) . body)
	     (let (first) (let* more . body)))))
	(define-syntax let
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     ((lambda (var ...) . body)
	      init ...))
	    ((_ name ((var init) ...) . body)
	     ((letrec ((name (lambda (var ...) . body)))
		name)
	      init ...))))
	(define-syntax case
	  (syntax-rules ()
	    ((_ x (test . exprs) ...)
	     (let ((key x))
	       (cond ((case-test key test) . exprs)
		     ...)))))
	(define-syntax case-test
	  (syntax-rules (else) ((_ k else) #t) ((_ k atoms) (memv k 'atoms))))
	(define-syntax cond
	  (syntax-rules (else =>)
	    ((_) #f)
	    ((_ (else . exps)) (begin #f . exps))
	    ((_ (x) . rest) (or x (cond . rest)))
	    ((_ (x => proc) . rest)
	     (let ((tmp x)) (cond (tmp (proc tmp)) . rest)))
	    ((_ (x . exps) . rest)
	     (if x (begin . exps) (cond . rest)))))
	(define-syntax and
	  (syntax-rules ()
	    ((_) #t)
	    ((_ test) test)
	    ((_ test . tests) (if test (and . tests) #f))))
	(define-syntax or
	  (syntax-rules ()
	    ((_) #f)
	    ((_ test) test)
	    ((_ test . tests) (let ((x test)) (if x x (or . tests))))))
	(define-syntax define
	  (syntax-rules ()
	    ((_ (var . args) . body)
	     (define var (lambda args . body)))
	    ((_ var init) (def var init))))
	(define-syntax if
	  (syntax-rules () ((_ x y ...) (if* x (lambda () y) ...))))
	(define-syntax delay
	  (syntax-rules () ((_ x) (delay* (lambda () x)))))))
    (define (if* a b . c) (if a (b) (if (pair? c) ((car c)))))
    (define (delay* thunk) (delay (thunk)))
    (define (null-env)
      ((eval `(lambda (cons append list->vector memv delay* if* syntax-rules**)
		((lambda (syntax-rules*)
		   (define-syntax syntax-rules
		     (syntax-rules* (get-env) #f (syntax ())
		       (syntax (((_ (lit ...) . rules)
				 (syntax-rules #f (lit ...) . rules))
				((_ ellipsis lits . rules)
				 (syntax-rules* (get-env) (syntax ellipsis)
				   (syntax lits) (syntax rules)))))))
		   ((lambda () ,@macro-defs (get-env))))
		 (syntax-rules** id? new-id ((get-env) (syntax ...)))))
	     #f)
       cons append list->vector memv delay* if* syntax-rules**))
    (define promise (delay (null-env)))
    (lambda (version)
      (if (= version 5)
          (force promise)
          (open-input-file "sheep-herders/r^-1rs.ltx")))))


(define scheme-report-environment
  (let-syntax
      ((extend-env
	(syntax-rules ()
	  ((extend-env env . names)
	   ((eval '(lambda names (get-env)) env)
	    . names)))))
    (let ()
      (define (r5-env)
	(extend-env (null-environment 5)
	  eqv? eq? equal?
	  number? complex? real? rational? integer? exact? inexact?
	  = < > <= >= zero? positive? negative? odd? even?
	  max min + * - /
	  abs quotient remainder modulo gcd lcm numerator denominator
	  floor ceiling truncate round rationalize
	  exp log sin cos tan asin acos atan sqrt expt
	  make-rectangular make-polar real-part imag-part magnitude angle
	  exact->inexact inexact->exact
	  number->string string->number
	  not boolean?
	  pair? cons car cdr set-car! set-cdr! caar cadr cdar cddr
	  caaar caadr cadar caddr cdaar cdadr cddar cdddr
	  caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
	  cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr
	  null? list? list length append reverse list-tail list-ref
	  memq memv member assq assv assoc
	  symbol? symbol->string string->symbol
	  char? char=? char<? char>? char<=? char>=?
	  char-ci=? char-ci<? char-ci>? char-ci<=? char-ci>=?
	  char-alphabetic? char-numeric? char-whitespace?
	  char-upper-case? char-lower-case?
	  char->integer integer->char char-upcase char-downcase
	  string? make-string string string-length string-ref string-set!
	  string=? string-ci=? string<? string>? string<=? string>=?
	  string-ci<? string-ci>? string-ci<=? string-ci>=?
	  substring string-append string->list list->string
	  string-copy string-fill!
	  vector? make-vector vector vector-length vector-ref vector-set!
	  vector->list list->vector vector-fill!
	  procedure? apply map for-each force
	  call-with-current-continuation
	  values call-with-values dynamic-wind
	  eval scheme-report-environment null-environment
	  call-with-input-file call-with-output-file
	  input-port? output-port? current-input-port current-output-port
	  with-input-from-file with-output-to-file
	  open-input-file open-output-file close-input-port close-output-port
	  read read-char peek-char eof-object? char-ready?
	  write display newline write-char))
      (define promise (delay (r5-env)))
      (lambda (version)
	(if (= version 5)
	    (force promise)
	    (open-input-file "sheep-herders/r^-1rs.ltx"))))))

;; [1] Some claim that this is not required, and that it is compliant for
;;
;;   (let* ((x (string #\a))
;;          (y (eval x (null-environment 5))))
;;     (string-set! x 0 #\b)
;;     y)
;;
;; to return "b", but I say that's as bogus as if
;;
;;   (let* ((x (string #\1))
;;          (y (string->number x)))
;;     (string-set! x 0 #\2)
;;     y)
;;
;; returned 2.  Most implementations disagree with me, however.
;;
;; Note: it would be fine to pass through those strings (and pairs and
;; vectors) that are immutable, but we can't portably detect them.


;; Repl provides a simple read-eval-print loop.  It semi-supports
;; top-level definitions and syntax definitions, but each one creates
;; a new binding whose region does not include anything that came
;; before the definition, so if you want mutually recursive top-level
;; procedures, you have to do it the hard way:
;;   (define f #f)
;;   (define (g) (f))
;;   (set! f (lambda () (g)))
;; Repl does not support macro uses that expand into top-level definitions.
(define (repl)
  (let repl ((env (scheme-report-environment 5)))
    (display "eiod> ")
    (let ((exp (read)))
      (if (not (eof-object? exp))
	  (case (and (pair? exp) (car exp))
	    ((define define-syntax) (repl (eval `(let () ,exp (get-env))
						env)))
	    (else
	     (for-each (lambda (val) (write val) (newline))
		       (call-with-values (lambda () (eval exp env))
			 list))
	     (repl env)))))))

(define (tests noisy)
  (define env (scheme-report-environment 5))
  (for-each
   (lambda (x)
     (let* ((exp (car x))
	    (expected (cadr x)))
       (if noisy (begin (display "Trying: ") (write exp) (newline)))
       (let* ((result (eval exp env))
	      (success (equal? result expected)))
	 (if (not success) 
	     (begin (display "Failed: ")
		    (if (not noisy) (write exp))
		    (display " returned ")
		    (write result)
		    (display ", not ")
		    (write expected)
		    (newline))))))
   '((1 1)
     (#t #t)
     ("hi" "hi")
     (#\a #\a)
     ('1 1)
     ('foo foo)
     ('(a b) (a b))
     ('#(a b) #(a b))
     (((lambda (x) x) 1) 1)
     ((+ 1 2) 3)
     (((lambda (x) (set! x 2) x) 1) 2)
     (((lambda () (define x 1) x)) 1)
     (((lambda () (define (x) 1) (x))) 1)
     ((begin 1 2) 2)
     (((lambda () (begin (define x 1)) x)) 1)
     (((lambda () (begin) 1)) 1)
     ((let-syntax ((f (syntax-rules () ((_) 1)))) (f)) 1)
     ((letrec-syntax ((f (syntax-rules () ((_) (f 1)) ((_ x) x)))) (f)) 1)
     ((let-syntax ((f (syntax-rules () ((_ x ...) '(x ...))))) (f 1 2)) (1 2))
     ((let-syntax ((f (syntax-rules ()
			((_ (x y) ...) '(x ... y ...))
			((_ x ...) '(x ...)))))
	(f (x1 y1) (x2 y2)))
      (x1 x2 y1 y2))
     ((let-syntax ((let (syntax-rules ()
			  ((_ ((var init) ...) . body)
			   '((lambda (var ...) . body) init ...)))))
	(let ((x 1) (y 2)) (+ x y)))
      ((lambda (x y) (+ x y)) 1 2))
     ((let ((x 1)) x) 1)
     ((let* ((x 1) (x (+ x 1))) x) 2)
     ((let ((call/cc call-with-current-continuation))
	(letrec ((x (call/cc list)) (y (call/cc list)))
	  (if (procedure? x) (x (pair? y))) 
	  (if (procedure? y) (y (pair? x)))
	  (let ((x (car x)) (y (car y)))
	    (and (call/cc x) (call/cc y) (call/cc x)))))
      #t)
     ((if 1 2) 2)
     ((if #f 2 3) 3)
     ((and 1 #f 2) #f)
     ((force (delay 1)) 1)
     ((let* ((x 0) (p (delay (begin (set! x (+ x 1)) x)))) (force p) (force p))
      1)
     ((let-syntax
	  ((foo (syntax-rules ()
		  ((_ (x ...) #(y z ...) ...)
		   '((z ...) ... #((x y) ...))))))
	(foo (a b c) #(1 i j) #(2 k l) #(3 m n)))
      ((i j) (k l) (m n) #((a 1) (b 2) (c 3))))
     ((do ((vec (make-vector 5))
	   (i 0 (+ i 1)))
	  ((= i 5) vec)
	(vector-set! vec i i))
      #(0 1 2 3 4))
     ((let-syntax ((f (syntax-rules (x) ((_ x) 1) ((_ y) 2))))
	(define x (f x))
	x)
      2)
     ((let-syntax ((f (syntax-rules () ((_) 'x)))) (f))
      x)
     ((let-syntax ((f (syntax-rules ()
			((_) (let ((x 1))
			       (let-syntax ((f (syntax-rules () ((_) 'x))))
				 (f)))))))
	(f))
      x)
     ((let-syntax
	  ((f (syntax-rules ()
		((f e a ...)
		 (let-syntax
		     ((g (syntax-rules ::: ()
			   ((g n :::) '((a e n :::) ...)))))
		   (g 1 2 3))))))
	(f ::: x y z))
      ((x ::: 1 2 3) (y ::: 1 2 3) (z ::: 1 2 3)))
     ((let-syntax ((m (syntax-rules () ((m x ... y) (y x ...)))))
	(m 1 2 3 -))
      -4))))

;; matching close paren for quote-and-evaluate at beginning of file.
) 

