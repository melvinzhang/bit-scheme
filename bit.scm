; Copyright (C) 1995 Danny Dube, Universite de Montreal. All rights reserved.

; Les fonctions utilitaires generales

; Suppose que les deux arguments sont deja des ensembles de symboles
(define symbol-set-union
  (lambda (ss1 ss2)
    (cond ((null? ss1)
	   ss2)
	  ((memq (car ss1) ss2)
	   (symbol-set-union (cdr ss1) ss2))
	  (else
	   (cons (car ss1) (symbol-set-union (cdr ss1) ss2))))))

(define symbol-set-intersection
  (lambda (ss1 ss2)
    (cond ((null? ss1)
	   '())
	  ((memq (car ss1) ss2)
	   (cons (car ss1) (symbol-set-intersection (cdr ss1) ss2)))
	  (else
	   (symbol-set-intersection (cdr ss1) ss2)))))

(define foldr
  (lambda (binop start l)
    (if (null? l)
	start
	(binop (car l) (foldr binop start (cdr l))))))

(define foldr1
  (lambda (binop l)
    (if (null? (cdr l))
	(car l)
	(binop (car l) (foldr1 binop (cdr l))))))

(define filter
  (lambda (pred? l)
    (cond ((null? l) '())
	  ((pred? (car l)) (cons (car l) (filter pred? (cdr l))))
	  (else (filter pred? (cdr l))))))

(define formals->varlist
  (lambda (formals)
    (cond ((symbol? formals)
	   (list formals))
	  ((null? formals)
	   '())
	  (else
	   (cons (car formals) (formals->varlist (cdr formals)))))))

(define prefix?
  (lambda (s1 s2)
    (let ((l1 (string-length s1))
	  (l2 (string-length s2)))
      (if (> l1 l2)
	  #f
	  (let loop ((i 0))
	    (cond ((= i l1)
		   #t)
		  ((char=? (string-ref s1 i) (string-ref s2 i))
		   (loop (+ i 1)))
		  (else
		   #f)))))))

(define unprefix
  (lambda (s1 s2)
    (let ((l1 (string-length s1)))
      (cond ((= l1 (string-length s2))
	     (string-append s1 "a"))
	    ((char=? #\a (string-ref s2 l1))
	     (string-append s1 "b"))
	    (else
	     (string-append s1 "a"))))))




; Initialiser les variables globales du programme

(define init-glob-vars
  (lambda ()
    (set! safe-name-memv                 '<memv>)
    (set! safe-name-make-promise '<make-promise>)
    (set! safe-name-list->vector '<list->vector>)
    (set! safe-name-list                 '<list>)
    (set! safe-name-append2           '<append2>)
    (set! safe-name-cons                 '<cons>)
    (set! gen-sym-pref   #f)
    (set! gen-sym-number  0)
    (set! libcprims       #f)
    (set! libalias        #f)
    (set! libclos         #f)
    (set! libpublics      #f)
    (set! libnames        #f)
    (set! apply1-cprim-no #f)
    (set! dirreq         #f)
    (set! allreq         #f)
    (set! req-clos-nodes #f)
    (set! const-counter 0)
    (set! const-alist '())
    (set! top-counter   0)
    (set! top-alist   '())
    (set! const-desc-string #f)
    (set! glob-counter  0)
    (set! glob-hidden '())
    (set! glob-public '())
    (set! glob-source '())
    (set! glob-v     '#())
    (set! glob-v-len    0)
    (set! phys-glob-no 0)
    (set! program-bytecode #f)
    (set! label-counter 0)
    (set! label-v    '#())
    (set! label-v-len   0)
    (set! flat-program-bytecode #f)
    (set! final-program-bytecode #f)
    (set! glob-var-init-codes #f)))




; Lire le programme source

(define read-source
  (lambda (name)
    (let ((port (open-input-file name)))
      (let loop ()
	(let ((exp (read port)))
	  (if (eof-object? exp)
	      (begin
		(close-input-port port)
		'())
	      (cons exp (loop))))))))




; Trouver des noms pour memv, make-promise, list->vector, list,
; append2 et cons. De cette facon, trans-case & cie plus loin
; pourront inserer un symbole representant une fonction
; du systeme aux endroits generes par les macros-expansion

(define safe-name-memv         '<memv>)
(define safe-name-make-promise '<make-promise>)
(define safe-name-list->vector '<list->vector>)
(define safe-name-list         '<list>)
(define safe-name-append2      '<append2>)
(define safe-name-cons         '<cons>)

; Cette fonction ne fonctionne que pour les struc. non-circ.
(define find-all-symbols
  (lambda (d)
    (cond ((symbol? d)
	   (list d))
	  ((pair? d)
	   (symbol-set-union (find-all-symbols (car d))
			     (find-all-symbols (cdr d))))
	  ((vector? d)
	   (let loop ((pos (- (vector-length d) 1)))
	     (if (< pos 0)
		 '()
		 (symbol-set-union (find-all-symbols (vector-ref d pos))
				   (loop (- pos 1))))))
	  (else
	   '()))))

; Trouver un prefixe unique pour avoir un gen-sym correct
(define find-uniq-prefix
  (lambda (ss)
    (let loop ((pref "") (names (map symbol->string ss)))
      (if (null? names)
	  pref
	  (let ((name (car names)))
	    (if (prefix? pref name)
		(loop (unprefix pref name) (cdr names))
		(loop pref (cdr names))))))))

; La fonction gen-sym
(define gen-sym-pref #f)
(define gen-sym-number 0)

(define gen-sym
  (lambda ()
    (let* ((str-num (number->string gen-sym-number))
	   (sym-name (string-append gen-sym-pref str-num))
	   (sym (string->symbol sym-name)))
      (set! gen-sym-number (+ gen-sym-number 1))
      sym)))




; Traduction des expressions Scheme en expressions plus simples
; Il ne reste que des references de var., des quotes, des literaux
; s'evaluant a eux-memes, des appels de procedure, des lambda exp.,
; des if, des set!, des begins, des defines se rapportant a des
; var. glob. uniquement

; A ne pas inserer dans la liste des translators
(define trans-define
  (lambda (l)
    (if (symbol? (cadr l))
	l
	(let ((procname (caadr l))
	      (formals (cdadr l))
	      (exps (cddr l)))
	  `(define ,procname (lambda ,formals ,@exps))))))

; A ne pas inserer dans la liste des translators
(define flatten-begin
  (lambda (expbegin)
    (cons 'begin
	  (let loop ((l (cdr expbegin)) (flat '()))
	    (if (null? l)
		flat
		(let ((tete (car l))
		      (queue (cdr l)))
		  (if (and (pair? tete) (eq? (car tete) 'begin))
		      (loop (cdr tete) (loop queue flat))
		      (cons tete (loop queue flat)))))))))

; A ne pas inserer dans la liste des translators
(define extract-define
  (lambda (lexp)
    (let ((tete (car lexp))
	  (reste (cdr lexp)))
      (if (and (pair? tete) (eq? (car tete) 'define))
	  (let ((result (extract-define reste)))
	    (cons (cons tete (car result)) (cdr result)))
	  (cons '() lexp)))))

; A ne pas inserer dans la liste des translators
(define trans-body
  (lambda (l)
    (let* ((flatbody (flatten-begin l))
	   (result (extract-define (cdr flatbody)))
	   (rawdefines (car result))
	   (exps (cdr result))
	   (defines (map trans-define rawdefines))
	   (decls (map cdr defines))
	   (body `(begin ,@exps)))
      (if (null? decls)
	  body
	  `(letrec ,decls ,body)))))

; A ne pas inserer dans la liste des translators
(define trans-lambda
  (lambda (l)
    (list 'lambda
	  (cadr l)
	  (trans-body (cons 'begin (cddr l))))))

; A ne pas inserer dans la liste des translators
(define trans-begin
  (lambda (l)
    (let ((flat (flatten-begin l)))
      (if (null? (cddr flat))
	  (cadr flat)
	  flat))))

; A ne pas inserer dans la liste des translators
(define trans-normal-let
  (lambda (l)
    (let* ((bindings (cadr l))
	   (body (cddr l))
	   (vars (map car bindings))
	   (inits (map cadr bindings)))
      `((lambda ,vars ,@body) ,@inits))))

; A ne pas inserer dans la liste des translators
(define trans-let-loop
  (lambda (l)
    (let* ((loop-name (cadr l))
	   (bindings (caddr l))
	   (body (cdddr l))
	   (vars (map car bindings))
	   (inits (map cadr bindings)))
      `((letrec ((,loop-name (lambda ,vars ,@body)))
	  ,loop-name)
	,@inits))))

(define trans-let
  (lambda (l)
    (if (symbol? (cadr l))
	(trans-let-loop l)
	(trans-normal-let l))))

(define trans-let*
  (lambda (l)
    (let ((bindings (cadr l))
	  (body (cddr l)))
      (if (or (null? bindings) (null? (cdr bindings)))
	  `(let ,bindings ,@body)
	  (let ((prem (car bindings))
		(reste (cdr bindings)))
	    `(let (,prem) (let* ,reste ,@body)))))))

(define trans-letrec
  (lambda (l)
    (let ((bindings (cadr l))
	  (body (cddr l)))
      (if (null? bindings)
	  `(let () ,@body)
	  (let* ((vars (map car bindings))
		 (inits (map cadr bindings))
		 (falsebind (map (lambda (v) `(,v #f)) vars))
		 (set!s (map (lambda (v i) `(set! ,v ,i)) vars inits)))
	    `(let ,falsebind
	       ,@set!s
	       (let () ,@body)))))))

(define trans-and
  (lambda (l)
    (cond ((null? (cdr l))
	   #t)
	  ((null? (cddr l))
	   (cadr l))
	  (else
	   `(if ,(cadr l) (and ,@(cddr l)) #f)))))

(define trans-or
  (lambda (l)
    (cond ((null? (cdr l))
	   #f)
	  ((null? (cddr l))
	   (cadr l))
	  (else
	   (let* ((e-hd (cadr l))
		  (e-tl (cddr l))
		  (tmp (gen-sym)))
	     `(let ((,tmp ,e-hd))
		(if ,tmp
		    ,tmp
		    (or ,@e-tl))))))))

(define trans-cond
  (lambda (l)
    (if (null? (cdr l))
	#f
	(let* ((clause (cadr l))
	       (autres (cddr l))
	       (newcond (cons 'cond autres)))
	  (cond ((eq? (car clause) 'else)
		 (cons 'begin (cdr clause)))
		((null? (cdr clause))
		 (list 'or (car clause) newcond))
		((eq? (cadr clause) '=>)
		 (let* ((test (car clause))
			(recipient (caddr clause))
			(tmp (gen-sym)))
		   `(let ((,tmp ,test))
		      (if ,tmp
			  (,recipient ,tmp)
			  ,newcond))))
		(else
		 (let* ((test (car clause))
			(actions (cdr clause))
			(conseq (cons 'begin actions)))
		   `(if ,test ,conseq ,newcond))))))))

(define trans-case
  (lambda (l)
    (let* ((tmp-key (gen-sym))
	   (trans-test
	    (lambda (test)
	      (if (eq? test 'else) 'else `(,safe-name-memv ,tmp-key ',test))))
	   (key (cadr l))
	   (clauses (cddr l))
	   (tests (map car clauses))
	   (expr-lists (map cdr clauses))
	   (memv-tests (map trans-test tests))
	   (cond-clauses (map cons memv-tests expr-lists)))
      `(let ((,tmp-key ,key)) (cond ,@cond-clauses)))))

(define trans-do
  (lambda (l)
    (let* ((normalize-step (lambda (v sf)
			     (if (null? sf) v (car sf))))
	   (bindings (cadr l))
	   (testnsequence (caddr l))
	   (commands (cdddr l))
	   (vars (map car bindings))
	   (inits (map cadr bindings))
	   (steps-fac (map cddr bindings))
	   (steps (map normalize-step vars steps-fac))
	   (test (car testnsequence))
	   (sequence (cdr testnsequence))
	   (loop-var (gen-sym))
	   (loop-call (cons loop-var steps))
	   (loop-bindings (map list vars inits)))
      `(let ,loop-var ,loop-bindings
	    (if ,test
		(begin
		  #f
		  ,@sequence)
		(begin
		  ,@commands
		  ,loop-call))))))

(define trans-delay
  (lambda (exp)
    (let ((delexp (cadr exp)))
      `(,safe-name-make-promise (lambda () ,delexp)))))

; A ne pas inclure dans la liste des translators
(define detect-unquote
  (lambda (exp level)
    (cond ((vector? exp)
	   (let loop ((pos (- (vector-length exp) 1)))
	     (cond ((< pos 0)
		    #f)
		   ((detect-unquote (vector-ref exp pos) level)
		    #t)
		   (else
		    (loop (- pos 1))))))
	  ((pair? exp)
	   (let ((tete (car exp)))
	     (cond ((eq? tete 'quasiquote)
		    (detect-unquote (cadr exp) (+ level 1)))
		   ((or (eq? tete 'unquote) (eq? tete 'unquote-splicing))
		    (if (= level 1)
			#t
			(detect-unquote (cadr exp) (- level 1))))
		   (else
		    (or (detect-unquote tete level)
			(detect-unquote (cdr exp) level))))))
	  (else
	   #f))))

(define trans-quasiquote
  (lambda (l)
    (let loop ((exp (cadr l)) (level 1))
      (cond ((not (detect-unquote exp level))
	     (list 'quote exp))
	    ((vector? exp)
	     (list safe-name-list->vector
		   (loop (vector->list exp) level)))
	    ((pair? exp)
	     (let ((tete (car exp)))
	       (cond ((eq? tete 'quasiquote)
		      (list safe-name-list
			    ''quasiquote
			    (loop (cadr exp) (+ level 1))))
		     ((eq? tete 'unquote)
		      (if (= level 1)
			  (cadr exp)
			  (list safe-name-list
				''unquote
				(loop (cadr exp) (- level 1)))))
		     ((and (pair? tete)
			   (eq? (car tete) 'unquote-splicing)
		           (= level 1))
		      (if (null? (cdr exp))
			  (cadr tete)
			  (list safe-name-append2
				(cadr tete)
				(loop (cdr exp) level))))
		     ((eq? tete 'unquote-splicing)
		      (list safe-name-list
			    ''unquote-splicing
			    (loop (cadr exp) (- level 1))))
		     (else
		      (list safe-name-cons
			    (loop (car exp) level)
			    (loop (cdr exp) level))))))))))

(define translators
  (list (cons 'let trans-let)
	(cons 'let* trans-let*)
	(cons 'letrec trans-letrec)
	(cons 'and trans-and)
	(cons 'or trans-or)
	(cons 'cond trans-cond)
	(cons 'case trans-case)
	(cons 'do trans-do)
	(cons 'delay trans-delay)
	(cons 'quasiquote trans-quasiquote)))

(define trans-sub
  (lambda (exp)
    (if (or (boolean? exp)
	    (symbol? exp)
	    (char? exp)
	    (number? exp)
	    (string? exp))
	exp
	(let ((tete (car exp)))
	  (cond ((eq? tete 'quote)
		 exp)
		((eq? tete 'lambda)
		 (let ((new-lambda (trans-lambda exp)))
		   (list 'lambda
			 (cadr new-lambda)
			 (trans-sub (caddr new-lambda)))))
		((eq? tete 'if)
		 (cons 'if (map trans-sub (cdr exp))))
		((eq? tete 'set!)
		 (list 'set! (cadr exp) (trans-sub (caddr exp))))
		((eq? tete 'begin)
		 (trans-begin (cons 'begin (map trans-sub (cdr exp)))))
		((eq? tete 'define)
		 (let ((new-define (trans-define exp)))
		   (list 'define
			 (cadr new-define)
			 (trans-sub (caddr new-define)))))
		(else
		 (let ((ass (assq tete translators)))
		   (if ass
		       (trans-sub ((cdr ass) exp))
		       (let ((new-exp (map trans-sub exp)))
			 (if (and (pair? (car new-exp))
				  (eq? (caar new-exp) 'lambda)
				  (null? (cadar new-exp)))
			     (caddar new-exp)
			     new-exp))))))))))




; Operations sur les nodes

(define make-cte-node
  (lambda (cte)                  (vector 0 cte #f)))
(define make-ref-node
  (lambda (symbol)               (vector 1 symbol #f #f #f)))
(define make-ref-node-full
  (lambda (symbol loc val glob?) (vector 1 symbol loc val glob?)))
(define make-lambda-node
  (lambda (formals body)         (vector 2 formals #f body #f)))
(define make-if-node
  (lambda (test conseq altern)   (vector 3 test conseq altern)))
(define make-set!-node
  (lambda (symbol exp)           (vector 4 symbol #f exp #f)))
(define make-begin-node
  (lambda (lexp)                 (vector 5 lexp)))
(define make-def-node
  (lambda (symbol exp)           (vector 6 symbol #f exp)))
(define make-call-node
  (lambda (op larg)              (vector 7 op larg)))
(define make-globdesc-node
  (lambda (symbol lib? nbaff)    (vector 8 symbol lib? nbaff #f #f #f)))

(define node-type
  (lambda (node)
    (vector-ref node 0)))

(define cte-node?      (lambda (node) (= (node-type node) 0)))
(define ref-node?      (lambda (node) (= (node-type node) 1)))
(define lambda-node?   (lambda (node) (= (node-type node) 2)))
(define if-node?       (lambda (node) (= (node-type node) 3)))
(define set!-node?     (lambda (node) (= (node-type node) 4)))
(define begin-node?    (lambda (node) (= (node-type node) 5)))
(define def-node?      (lambda (node) (= (node-type node) 6)))
(define call-node?     (lambda (node) (= (node-type node) 7)))
(define globdesc-node? (lambda (node) (= (node-type node) 8)))

(define getter1 (lambda (node) (vector-ref node 1)))
(define getter2 (lambda (node) (vector-ref node 2)))
(define getter3 (lambda (node) (vector-ref node 3)))
(define getter4 (lambda (node) (vector-ref node 4)))
(define getter5 (lambda (node) (vector-ref node 5)))
(define getter6 (lambda (node) (vector-ref node 6)))

(define get-cte     getter1)
(define get-no      getter2)
(define get-symbol  getter1)
(define get-loc     getter2)
(define get-val     getter3)
(define get-glob?   getter4)
(define get-formals getter1)
(define get-fdesc   getter2)
(define get-body    getter3)
(define get-label   getter4)
(define get-test    getter1)
(define get-conseq  getter2)
(define get-altern  getter3)
(define get-exp     getter3)
(define get-lexp    getter1)
(define get-op      getter1)
(define get-larg    getter2)
(define get-lib?    getter2)
(define get-nbaff   getter3)
(define get-init    getter4)
(define get-libno   getter5)
(define get-srcno   getter6)

(define setter1 (lambda (node val) (vector-set! node 1 val)))
(define setter2 (lambda (node val) (vector-set! node 2 val)))
(define setter3 (lambda (node val) (vector-set! node 3 val)))
(define setter4 (lambda (node val) (vector-set! node 4 val)))
(define setter5 (lambda (node val) (vector-set! node 5 val)))
(define setter6 (lambda (node val) (vector-set! node 6 val)))

(define set-no!    setter2)
(define set-glob?! setter4)
(define set-loc!   setter2)
(define set-fdesc! setter2)
(define set-nbaff! setter3)
(define set-init!  setter4)
(define set-op!    setter1)
(define set-val!   setter3)
(define set-libno! setter5)
(define set-srcno! setter6)
(define set-label! setter4)




; Transformation du code source en noeuds fonctionnels.

(define lnode #f)

(define exp->node
  (lambda (exp)
    (cond ((or (boolean? exp) (char? exp) (number? exp) (string? exp))
	   (make-cte-node exp))
	  ((symbol? exp)
	   (make-ref-node exp))
	  (else  ; pair
	   (let ((tete (car exp)))
	     (cond ((eq? tete 'quote)
		    (make-cte-node (cadr exp)))
		   ((eq? tete 'lambda)
		    (make-lambda-node (cadr exp) (exp->node (caddr exp))))
		   ((eq? tete 'if)
		    (make-if-node (exp->node (cadr exp))
				  (exp->node (caddr exp))
				  (exp->node
				   (if (null? (cdddr exp)) #f (cadddr exp)))))
		   ((eq? tete 'set!)
		    (make-set!-node (cadr exp) (exp->node (caddr exp))))
		   ((eq? tete 'begin)
		    (make-begin-node (map exp->node (cdr exp))))
		   ((eq? tete 'define)
		    (make-def-node (cadr exp) (exp->node (caddr exp))))
		   (else  ; procedure call
		    (make-call-node (exp->node (car exp))
				    (map exp->node (cdr exp))))))))))




; Ramassage des variables globales definies, modifiees ou lues

(define extract-glob-names
  (let ((action-v
	 (vector
	  (lambda (node loop env)  ; cte
	    '())
	  (lambda (node loop env)  ; ref
	    (let ((refsym (get-symbol node)))
	      (if (memq refsym env)
		  '()
		  (list refsym))))
	  (lambda (node loop env)  ; lambda
	    (loop (get-body node)
		  (symbol-set-union env (formals->varlist
					 (get-formals node)))))
	  (lambda (node loop env)  ; if
	    (let ((test-globs (loop (get-test node) env))
		  (conseq-globs (loop (get-conseq node) env))
		  (altern-globs (loop (get-altern node) env)))
	      (symbol-set-union (symbol-set-union test-globs conseq-globs)
				altern-globs)))
	  (lambda (node loop env)  ; set!
	    (let* ((set!sym (get-symbol node))
		   (l (if (memq set!sym env) '() (list set!sym))))
	      (symbol-set-union l (loop (get-exp node) env))))
	  (lambda (node loop env)  ; begin
	    (let* ((lnode (get-lexp node))
		   (llglob (map (lambda (node) (loop node env)) lnode)))
	      (foldr1 symbol-set-union llglob)))
	  (lambda (node loop env)  ; def
	    (symbol-set-union (list (get-symbol node))
			      (loop (get-exp node) env)))
	  (lambda (node loop env)  ; call
	    (let* ((lnode (cons (get-op node) (get-larg node)))
		   (llglob (map (lambda (node) (loop node env)) lnode)))
	      (foldr1 symbol-set-union llglob))))))
    (lambda (node)
      (let loop ((node node) (env '()))
	((vector-ref action-v (node-type node)) node loop env)))))




; Chargement de la librairie

(define libcprims #f)
(define libalias #f)
(define libclos #f)
(define libpublics #f)
(define libnames #f)
(define apply1-cprim-no #f)

(define read-lib
  (lambda (libname)
    (let ((port (open-input-file libname)))
      (let loop1 ((n 0))
	(if (= n 4)
	    (begin
	      (close-input-port port)
	      '())
	    (let loop2 ()
	      (let* ((datum (read port)))
		(if datum
		    (let ((reste (loop2)))
		      (cons (cons datum (car reste)) (cdr reste)))
		    (cons '() (loop1 (+ n 1)))))))))))

(define get-lib-cprims
  (lambda (libpart1)
    (map (lambda (def)
	   (let ((name (car def))
		 (no (cdr def)))
	     (if (eq? name 'apply1)
		 (set! apply1-cprim-no no))
	     (cons name no)))
	 libpart1)))

(define get-lib-alias
  (lambda (libpart2 libpart3 libpart4)
    (let* ((defs (append libpart2 libpart3 libpart4))
	   (defals (filter (lambda (def)
			     (and (not (symbol? def))
				  (symbol? (caddr def))))
			   defs)))
      (map (lambda (defal) (cons (cadr defal) (caddr defal))) defals))))

(define get-lib-clos
  (lambda (libpart2 libpart3 libpart4)
    (let* ((defs (append libpart2 libpart3 libpart4))
	   (defcls (filter (lambda (def)
			     (and (not (symbol? def))
				  (not (symbol? (caddr def)))))
			   defs)))
      (map (lambda (defcl) (cons (cadr defcl) (caddr defcl))) defcls))))

(define get-lib-publics
  (lambda (libpart3 libpart4)
    (map (lambda (sym-or-def)
	   (if (symbol? sym-or-def)
	       sym-or-def
	       (cadr sym-or-def)))
	 (append libpart3 libpart4))))

(define get-lib-names
  (lambda (libpart1 libpart2 libpart3 libpart4)
    (let* ((cprim-names (map car libpart1))
	   (defs (append libpart2 libpart3 libpart4))
	   (truedefs (filter (lambda (def) (not (symbol? def))) defs)))
      (append cprim-names (map cadr truedefs)))))

(define load-lib
  (lambda ()
    (let* ((alllib (read-lib "librairie.scm"))
	   (libpart1 (list-ref alllib 0))
	   (libpart2 (list-ref alllib 1))
	   (libpart3 (list-ref alllib 2))
	   (libpart4 (list-ref alllib 3)))
      (set! libcprims (get-lib-cprims libpart1))
      (set! libalias (get-lib-alias libpart2 libpart3 libpart4))
      (set! libclos (get-lib-clos libpart2 libpart3 libpart4))
      (set! libpublics (get-lib-publics libpart3 libpart4))
      (set! libnames (get-lib-names libpart1 libpart2 libpart3 libpart4)))))




; Capture de la librairie necessaire

(define dirreq #f)
(define allreq #f)
(define req-clos-nodes #f)

(define grab-lib
  (lambda (dirreq)
    (let loop ((toadd dirreq) (added '()) (clos-nodes '()))
      (cond ((null? toadd)
	     (set! allreq added)
	     (set! req-clos-nodes clos-nodes))
	    ((memq (car toadd) added)
	     (loop (cdr toadd) added clos-nodes))
	    (else
	     (let* ((newfun (car toadd))
		    (ass-cprim (assq newfun libcprims)))
	       (if ass-cprim
		   (loop (cdr toadd)
			 (cons newfun added)
			 clos-nodes)
		   (let ((ass-alias (assq newfun libalias)))
		     (if ass-alias
			 (loop (cons (cdr ass-alias) (cdr toadd))
			       (cons newfun added)
			       clos-nodes)
			 (let ((ass-clos (assq newfun libclos)))
			   (let* ((code (cdr ass-clos))
				  (sub-code (trans-sub code))
				  (node (exp->node sub-code))
				  (node-globs (extract-glob-names node))
				  (new-clos (cons newfun node)))
			     (loop (append node-globs (cdr toadd))
				   (cons newfun added)
				   (cons new-clos clos-nodes)))))))))))))




; Ramassage et codage des constantes du programme source

(define const-counter 0)
(define const-alist '())
; Chaque ass: (original numero . desc)
(define top-counter 0)
(define top-alist '())
; Chaque ass: (const-no . top-const-no)
(define const-desc-string #f)

(define const-no
  (lambda (d)
    (let ((ass (assoc d const-alist)))
      (if ass
	  (cadr ass)
	  (begin
	    (cond ((or (null? d) (boolean? d) (char? d) (number? d))
		   (set! const-alist
			 (cons (cons d (cons const-counter d)) const-alist)))
		  ((pair? d)
		   (let* ((leftno (const-no (car d)))
			  (rightno (const-no (cdr d)))
			  (desc (cons leftno rightno)))
		     (set! const-alist (cons (cons d (cons const-counter desc))
					     const-alist))))
		  ((string? d)
		   (set! const-alist
			 (cons (cons d (cons const-counter d)) const-alist)))
		  ((symbol? d)
		   (let* ((nom (symbol->string d))
			  (nomno (const-no nom))
			  (desc (string->symbol (number->string nomno))))
		     (set! const-alist (cons (cons d (cons const-counter desc))
					     const-alist))))
		  ((vector? d)
		   (let* ((listd (vector->list d))
			  (listno (map const-no listd))
			  (desc (list->vector listno)))
		     (set! const-alist (cons (cons d (cons const-counter desc))
					     const-alist)))))
	    (set! const-counter (+ const-counter 1))
	    (- const-counter 1))))))

(define top-const-no
  (lambda (d)
    (if (or (null? d) (boolean? d) (char? d) (number? d))
	#f
	(let* ((cno (const-no d))
	       (ass (assv cno top-alist)))
	  (if ass
	      (cdr ass)
	      (begin
		(set! top-alist (cons (cons cno top-counter) top-alist))
		(set! top-counter (+ top-counter 1))
		(- top-counter 1)))))))

(define code-abs-number
  (lambda (n)
    (let* ((msb (quotient n 256))
	   (lsb (modulo n 256))
	   (msc (integer->char msb))
	   (lsc (integer->char lsb)))
      (string msc lsc))))

(define code-one-const
  (lambda (desc)
    (cond ((null? desc)
	   "0")                              ; 0 pour EMPTY
	  ((pair? desc)
	   (string-append "1"                ; 1 pour PAIR
			  (code-abs-number (car desc))
			  (code-abs-number (cdr desc))))
	  ((boolean? desc)
	   (if desc "2t" "2f"))              ; 2 pour BOOLEAN
	  ((char? desc)
	   (string #\3 desc))                ; 3 pour CHAR
	  ((string? desc)
	   (string-append "4"                ; 4 pour STRING
			  (code-abs-number (string-length desc))
			  desc))
	  ((symbol? desc)
	   (string-append "5"                ; 5 pour SYMBOL
			  (code-abs-number
			   (string->number (symbol->string desc)))))
	  ((number? desc)
	   (string-append "6"                ; 6 pour NUMBER
			  (if (< desc 0) "-" "+")
			  (code-abs-number (abs desc))))
	  ((vector? desc)
	   (let* ((listref (vector->list desc))
		  (listcodes (map code-abs-number listref))
		  (listallcodes
		   (cons "7"                 ; 7 pour VECTOR
			 (cons (code-abs-number (vector-length desc))
			       listcodes))))
	     (apply string-append listallcodes))))))

(define code-in-const
  (lambda (nbconst const-alist)
    (let* ((right-alist (reverse const-alist))
	   (listdesc (map cddr right-alist))
	   (listcodes (map code-one-const listdesc))
	   (listallcodes (cons (code-abs-number nbconst) listcodes)))
      (apply string-append listallcodes))))

(define code-top-const
  (lambda (nbtop top-alist)
    (let* ((right-alist (reverse top-alist))
	   (listtop (map car right-alist))
	   (listcodes (map code-abs-number listtop))
	   (listallcodes (cons (code-abs-number nbtop) listcodes)))
      (apply string-append listallcodes))))

(define code-const
  (lambda ()
    (string-append (code-in-const const-counter const-alist)
		   (code-top-const top-counter top-alist))))




; Enregistrement des variables globales

(define glob-counter 0)
(define glob-hidden '())  ; Variables cachees de la librairie
(define glob-public '())  ; Variables visibles de la librairie
(define glob-source '())  ; Variables introduites par le source
; Chaque assoc: (nom . numero)
(define glob-v '#())
(define glob-v-len 0)

(define glob-var-no
  (lambda (name lib?)
    (or
     (cond ((memq name libpublics)
	    (let ((ass (assq name glob-public)))
	      (if ass
		  (cdr ass)
		  (let ((newass (cons name glob-counter)))
		    (set! glob-public (cons newass glob-public))
		    #f))))
	   (lib?
	    (let ((ass (assq name glob-hidden)))
	      (if ass
		  (cdr ass)
		  (let ((newass (cons name glob-counter)))
		    (set! glob-hidden (cons newass glob-hidden))
		    #f))))
	   (else
	    (let ((ass (assq name glob-source)))
	      (if ass
		  (cdr ass)
		  (let ((newass (cons name glob-counter)))
		    (set! glob-source (cons newass glob-source))
		    #f)))))
     (begin
       (if (= glob-counter glob-v-len)
	   (let* ((newlen (+ (* 2 glob-v-len) 1))
		  (newv (make-vector newlen)))
	     (let loop ((pos 0))
	       (if (< pos glob-v-len)
		   (begin
		     (vector-set! newv pos (vector-ref glob-v pos))
		     (loop (+ pos 1)))))
	     (set! glob-v newv)
	     (set! glob-v-len newlen)))
       (vector-set! glob-v glob-counter (make-globdesc-node name lib? 0))
       (set! glob-counter (+ glob-counter 1))
       (- glob-counter 1)))))




; Localisation des variables

; Un resultat (glob . name) signifie que name est globale
; Un resultat (lex #frame . #offset) donne le numero de frame et la
;     position sur ce frame
; Un resultat (lex #frame . #f) indique que name est seule sur son frame
(define where-var
  (lambda (name env)
    (if (null? env)
	(cons 'glob name)
	(let* ((locals (car env))
	       (membership (memq name locals)))
	  (if membership
	      (let* ((nblocals (length locals))
		     (pos (- nblocals (length membership)))
		     (declpos (if (= nblocals 1) #f pos)))
		(cons 'lex (cons 0 declpos)))
	      (let ((result (where-var name (cdr env))))
		(if (eq? (car result) 'glob)
		    result
		    (let ((frame (cadr result))
			  (offset (cddr result)))
		      (cons 'lex (cons (+ frame 1) offset))))))))))




; Parcours des noeuds pour:
;     Numeroter les constantes si nec.
;     Identifier chaque variable
;     Compter les definitions et affectations des var. glob
;     Resumer les parametres formels

(define traverse1-cte-node
  (lambda (node env lib?)
    (set-no! node (top-const-no (get-cte node)))))

(define traverse1-ref-node
  (lambda (node env lib?)
    (let* ((name (get-symbol node))
	   (pos (where-var name env))
	   (glob? (eq? (car pos) 'glob))
	   (loc (if glob? (glob-var-no name lib?) (cdr pos))))
      (set-glob?! node glob?)
      (set-loc! node loc))))

(define formals->fdesc
  (lambda (formals)
    (let loop ((nbreq 0) (formals formals))
      (cond ((null? formals)
	     (cons nbreq #f))
	    ((symbol? formals)
	     (cons nbreq #t))
	    (else
	     (loop (+ nbreq 1) (cdr formals)))))))

(define traverse1-lambda-node
  (lambda (node env lib?)
    (let* ((formals (get-formals node))
	   (varlist (formals->varlist formals))
	   (newenv (if (null? varlist) env (cons varlist env)))
	   (fdesc (formals->fdesc formals)))
      (set-fdesc! node fdesc)
      (traverse1-node (get-body node) newenv lib?))))

(define traverse1-if-node
  (lambda (node env lib?)
    (traverse1-node (get-test node)   env lib?)
    (traverse1-node (get-conseq node) env lib?)
    (traverse1-node (get-altern node) env lib?)))

(define traverse1-set!-node
  (lambda (node env lib?)
    (let* ((name (get-symbol node))
	   (pos (where-var name env))
	   (glob? (eq? (car pos) 'glob))
	   (loc (if glob? (glob-var-no name lib?) (cdr pos))))
      (set-glob?! node glob?)
      (set-loc! node loc)
      (if glob?
	  (let* ((desc (vector-ref glob-v loc))
		 (oldnb (get-nbaff desc)))
	    (set-nbaff! desc (+ oldnb 2)))))  ; Declare la var. mut.
    (traverse1-node (get-exp node) env lib?)))

(define traverse1-begin-node
  (lambda (node env lib?)
    (let ((lnode (get-lexp node)))
      (for-each (lambda (node) (traverse1-node node env lib?)) lnode))))

(define traverse1-def-node
  (lambda (node env lib?)
    (let* ((loc (glob-var-no (get-symbol node) lib?))
	   (desc (vector-ref glob-v loc))
	   (oldnb (get-nbaff desc)))
      (set-loc! node loc)
      (set-nbaff! desc (+ oldnb 1)))
    (traverse1-node (get-exp node) env lib?)))

(define traverse1-call-node
  (lambda (node env lib?)
    (let ((lnode (get-larg node)))
      (traverse1-node (get-op node) env lib?)
      (for-each (lambda (node) (traverse1-node node env lib?)) lnode))))

(define traverse1-node
  (let ((action-v
	 (vector
	  traverse1-cte-node
	  traverse1-ref-node
	  traverse1-lambda-node
	  traverse1-if-node
	  traverse1-set!-node
	  traverse1-begin-node
	  traverse1-def-node
	  traverse1-call-node)))
    (lambda (node env lib?)
      ((vector-ref action-v (node-type node)) node env lib?))))

(define traverse1
  (lambda ()
    (for-each
     (lambda (name)
       (let* ((no (glob-var-no name #t))
	      (desc (vector-ref glob-v no)))
	 (set-nbaff! desc 1)))
     allreq)
    (for-each (lambda (node) (traverse1-node node '() #t))
	      (map cdr req-clos-nodes))
    (for-each (lambda (node) (traverse1-node node '() #f))
	      lnode)))




; Determiner la valeur initiale des fonctions de la librairie

(define find-an-init
  (lambda (name)
    (let ((asscprim (assq name libcprims)))
      (if asscprim
	  (cons 'cprim (cdr asscprim))
	  (let ((assalias (assq name libalias)))
	    (if assalias
		(find-an-init (cdr assalias))
		(let ((node (cdr (assq name req-clos-nodes))))
		  (if (lambda-node? node)
		      (cons 'clos node)
		      (begin
			(display "Error: fonct. de la lib. a env. non-vide: ")
			(write name)
			(newline)
			(cons 'clos 0))))))))))

(define find-inits
  (lambda ()
    (let loop ((no 0))
      (if (< no glob-counter)
	  (let ((desc (vector-ref glob-v no)))
	    (if (get-lib? desc)
		(let* ((name (get-symbol desc))
		       (init (find-an-init name)))
		  (set-init! desc init)))
	    (loop (+ no 1)))))))




; Parcours des noeuds pour:
;     Resoudre a priori certaines references
;     "Inliner" lorsque possible

(define reduce-list
  '((append      2 append2)
    (=           2 math=2)
    (<           2 math<2)
    (>           2 math>2)
    (<=          2 math<=2)
    (>=          2 math>=2)
    (max         2 max2)
    (min         2 min2)
    (+           2 math+2)
    (*           2 math*2)
    (-           2 math-2)
    (/           2 quotient)
    (gcd         2 mathgcd2)
    (lcm         2 mathlcm2)
    (make-string 1 make-string1)
    (make-vector 1 make-vector1)
    (apply       2 apply1)
    (map         2 map1)))

(define reduced-function
  (lambda (name nbargs)
    (let ((rule (assq name reduce-list)))
      (if (not rule)
	  #f
	  (if (= nbargs (cadr rule))
	      (caddr rule)
	      #f)))))

(define optimize-call
  (lambda (node match)
    (let* ((symbol-field match)
	   (glob?-field  #t)
	   (loc-field    (glob-var-no match #t))
	   (var-desc     (vector-ref glob-v loc-field))
	   (val-field    (get-init var-desc))
	   (new-op       (make-ref-node-full symbol-field
					     loc-field
					     val-field
					     glob?-field)))
      (set-op! node new-op))))

(define reduce-call
  (lambda (node)
    (let* ((op (get-op node))
	   (name (get-symbol op))
	   (nbargs (length (get-larg node)))
	   (match (reduced-function name nbargs)))
      (if match (optimize-call node match)))))

(define traverse2-cte-node
  (lambda (node lib?)
    #t))

(define traverse2-ref-node
  (lambda (node lib?)
    (if (get-glob? node)
	(set-val! node
		  (let* ((vardesc (vector-ref glob-v (get-loc node)))
			 (varinit (get-init vardesc)))
		    (if lib?
			varinit
			(if (not (get-lib? vardesc))
			    #f
			    (if (> (get-nbaff vardesc) 1)
				#f
				varinit))))))))

(define traverse2-lambda-node
  (lambda (node lib?)
    (traverse2-node (get-body node) lib?)))

(define traverse2-if-node
  (lambda (node lib?)
    (traverse2-node (get-test node) lib?)
    (traverse2-node (get-conseq node) lib?)
    (traverse2-node (get-altern node) lib?)))

(define traverse2-set!-node
  (lambda (node lib?)
    (traverse2-node (get-exp node) lib?)))

(define traverse2-begin-node
  (lambda (node lib?)
    (for-each (lambda (node) (traverse2-node node lib?))
	      (get-lexp node))))

(define traverse2-def-node
  (lambda (node lib?)
    (traverse2-node (get-exp node) lib?)))

(define traverse2-call-node
  (lambda (node lib?)
    (let ((op (get-op node)))
      (traverse2-node op lib?)
      (for-each (lambda (node) (traverse2-node node lib?))
		(get-larg node))
      (if (and (ref-node? op) (get-glob? op) (get-val op))
	  (reduce-call node)))))

(define traverse2-node
  (let ((action-v
	 (vector
	  traverse2-cte-node
	  traverse2-ref-node
	  traverse2-lambda-node
	  traverse2-if-node
	  traverse2-set!-node
	  traverse2-begin-node
	  traverse2-def-node
	  traverse2-call-node)))
    (lambda (node lib?)
      ((vector-ref action-v (node-type node)) node lib?))))

(define traverse2
  (lambda ()
    (for-each (lambda (node) (traverse2-node node #t))
	      (map cdr req-clos-nodes))
    (for-each (lambda (node) (traverse2-node node #f))
	      lnode)))




; Assigner des numeros physiques aux variables

(define phys-glob-no 0)

(define gen-phys-no
  (lambda ()
    (set! phys-glob-no (+ phys-glob-no 1))
    (- phys-glob-no 1)))

(define assign-phys-no
  (lambda ()
    (let loop ((no 0))
      (if (< no glob-counter)
	  (let* ((desc (vector-ref glob-v no))
		 (libvar? (get-lib? desc))
		 (mutvar? (> (get-nbaff desc) 1)))
	    (cond ((not libvar?)
		   (let ((phys-no (gen-phys-no)))
		     (set-libno! desc phys-no)
		     (set-srcno! desc phys-no)))
		  (mutvar?
		   (set-libno! desc (gen-phys-no))
		   (set-srcno! desc (gen-phys-no)))
		  (else
		   (let ((phys-no (gen-phys-no)))
		     (set-libno! desc phys-no)
		     (set-srcno! desc phys-no))))
	    (loop (+ no 1)))))))




; Gestion des labels

(define label-counter 0)
(define label-v '#())
(define label-v-len 0)

(define make-label
  (lambda ()
    (if (= label-counter label-v-len)
	(let* ((newlen (+ (* label-v-len 2) 1))
	       (newv (make-vector newlen)))
	  (let loop ((pos 0))
	    (if (< pos label-counter)
		(begin
		  (vector-set! newv pos (vector-ref label-v pos))
		  (loop (+ pos 1)))))
	  (set! label-v newv)
	  (set! label-v-len newlen)))
    (set! label-counter (+ label-counter 1))
    (- label-counter 1)))




; Generation du byte-code

(define program-bytecode #f)
(define flat-program-bytecode #f)
(define final-program-bytecode #f)

(define bcompile-no
  (lambda (no)
    (let ((msb (quotient no 256))
	  (lsb (modulo no 256)))
      (list msb lsb))))

(define bcompile-cte-null     ; 27 pour ()
  (lambda ()
    '(27)))

(define bcompile-cte-boolean  ; 28 pour #f, 29 pour #t
  (lambda (b)
    (if b '(29) '(28))))

(define bcompile-cte-char     ; 30 pour char
  (lambda (c)
    (list 30 (char->integer c))))

(define bcompile-cte-number   ; courts: + 31 - 32, longs: + 33 - 34
  (lambda (n)
    (if (>= n 0)
	(if (< n 256)
	    (list 31 n)
	    (list 33 (bcompile-no n)))
	(if (< (- n) 256)
	    (list 32 (- n))
	    (list 34 (bcompile-no (- n)))))))

(define bcompile-cte-imm
  (lambda (cte)
    (cond ((null? cte)
	   (bcompile-cte-null))
	  ((boolean? cte)
	   (bcompile-cte-boolean cte))
	  ((char? cte)
	   (bcompile-cte-char cte))
	  (else
	   (bcompile-cte-number cte)))))

(define bcompile-cte-built
  (lambda (no)
    (if (< no 256)
	(list 0 no)
	(list 1 (bcompile-no no)))))

(define bcompile-cte
  (lambda (node tail? lib?)
    (let* ((const-no (get-no node))
	   (get-cte-bc (if const-no
			   (bcompile-cte-built const-no)
			   (bcompile-cte-imm (get-cte node)))))
      (if tail? (list get-cte-bc 14) get-cte-bc))))

(define special-lex-pos
  (lambda (frame offset)
    (case frame
      ((0)  (case offset ((0) 0) ((1) 1) ((2) 2) (else #f)))
      ((1)  (case offset ((0) 3) ((1) 4) (else #f)))
      ((2)  (case offset ((0) 5) (else #f)))
      (else #f))))

(define bcompile-ref-lex
  (lambda (node)
    (let* ((loc (get-loc node))
	   (frame (car loc))
	   (offset (cdr loc))
	   (spec (special-lex-pos frame (if offset offset 0))))
      (cond (spec
	     (list (+ spec 36)))
	    (offset
	     (if (and (< frame 256) (< offset 256))
		 (list 2 frame offset)
		 (list 3 (bcompile-no frame) (bcompile-no offset))))
	    (else
	     (if (< frame 256)
		 (list 2 frame)
		 (list 3 (bcompile-no frame))))))))

(define bcompile-ref-glob
  (lambda (node lib?)
    (let* ((loc (get-loc node))
	   (vardesc (vector-ref glob-v loc))
	   (phys-no (if lib? (get-libno vardesc) (get-srcno vardesc))))
      (if (< phys-no 256)
	  (list 4 phys-no)
	  (list 5 (bcompile-no phys-no))))))

(define bcompile-ref
  (lambda (node tail? lib?)
    (let ((result (if (get-glob? node)
		      (bcompile-ref-glob node lib?)
		      (bcompile-ref-lex node))))
      (if tail? (list result 14) result))))

(define bcompile-set!-lex
  (lambda (node)
    (let* ((loc (get-loc node))
	   (frame (car loc))
	   (offset (cdr loc)))
      (if offset
	  (if (and (< frame 256) (< offset 256))
	      (list 6 frame offset)
	      (list 7 (bcompile-no frame) (bcompile-no offset)))
	  (if (< frame 256)
	      (list 6 frame)
	      (list 7 (bcompile-no frame)))))))

(define bcompile-set!-glob
  (lambda (node lib?)
    (let* ((loc (get-loc node))
	   (vardesc (vector-ref glob-v loc))
	   (phys-no (if lib? (get-libno vardesc) (get-srcno vardesc))))
      (if (< phys-no 256)
	  (list 8 phys-no)
	  (list 9 (bcompile-no phys-no))))))

(define bcompile-set!
  (lambda (node tail? lib?)
    (let* ((exp (get-exp node))
	   (exp-bc (bcompile exp #f lib?))
	   (aff-bc (if (get-glob? node)
		       (bcompile-set!-glob node lib?)
		       (bcompile-set!-lex node)))
	   (set!-bc (list exp-bc aff-bc)))
      (if tail? (list set!-bc 14) set!-bc))))

(define bcompile-def
  (lambda (node tail? lib?)
    (let* ((exp (get-exp node))
	   (exp-bc (bcompile exp #f lib?))
	   (aff-bc (bcompile-set!-glob node lib?))
	   (def-bc (list exp-bc aff-bc)))
      (if tail? (list def-bc 14) def-bc))))

(define bcompile-pop-n
  (lambda (n)
    (cond ((= n 1)
	   '(51))
	  ((< n 256)
	   (list 49 n))
	  (else
	   (list 50 (bcompile-no n))))))

(define bcompile-begin
  (lambda (node tail? lib?)
    (let loop ((lexp (get-lexp node)) (nb-prev 0))
      (if (null? (cdr lexp))
	  (list (bcompile-pop-n nb-prev)
		(bcompile (car lexp) tail? lib?))
	  (list (bcompile (car lexp) #f lib?)
		(loop (cdr lexp) (+ nb-prev 1)))))))

(define bcompile-label-def
  (lambda (no)
    (list 'def no)))

(define bcompile-label-ref
  (lambda (no)
    (list 'ref no)))

(define bcompile-if
  (lambda (node tail? lib?)
    (let* ((debut-altern    (make-label))
	   (fin-altern      (if tail? #f (make-label)))
	   (test-bc         (bcompile (get-test node) #f lib?))
	   (cjump-bc        (list 11 (bcompile-label-ref debut-altern)))
	   (conseq-bc       (bcompile (get-conseq node) tail? lib?))
	   (ujump-bc        (if tail?
				'()
				(list 12 (bcompile-label-ref fin-altern))))
	   (debut-altern-bc (bcompile-label-def debut-altern))
	   (altern-bc       (bcompile (get-altern node) tail? lib?))
	   (fin-altern-bc   (if tail?
				'()
				(bcompile-label-def fin-altern))))
      (list test-bc cjump-bc conseq-bc ujump-bc
	    debut-altern-bc altern-bc fin-altern-bc))))

(define bcompile-make-frame
  (lambda (fdesc)
    (let* ((nbreq (car fdesc))
	   (fac? (cdr fdesc))
	   (frame-size (+ nbreq (if fac? 1 0))))
      (cond ((= frame-size 0)
	     '())
	    ((and (= frame-size 1) (not fac?))
	     '(42))
	    ((and (= frame-size 2) (not fac?))
	     '(43))
	    ((and (= frame-size 1) fac?)
	     '(44))
	    (fac?
	     (if (< frame-size 256)
		 (list 22 frame-size)
		 (list 23 (bcompile-no frame-size))))
	    (else
	     (if (< frame-size 256)
		 (list 20 frame-size)
		 (list 21 (bcompile-no frame-size))))))))

(define bcompile-closure
  (lambda (node lib?)
    (let* ((fdesc (get-fdesc node))
	   (make-frame-bc (bcompile-make-frame fdesc))
	   (body-bc (bcompile (get-body node) #t lib?)))
      (list make-frame-bc body-bc))))

(define bcompile-lambda
  (lambda (node tail? lib?)
    (let ((clos-bc (bcompile-closure node lib?)))
      (if tail?
	  (list 10 clos-bc)
	  (let* ((suite (make-label))
		 (make-clos-bc (list 48 (bcompile-label-ref suite)))
		 (suite-bc (bcompile-label-def suite)))
	    (list make-clos-bc clos-bc suite-bc))))))

(define bcompile-calc-args
  (lambda (larg lib?)
    (let loop ((larg larg) (prev-args-bc '()))
      (if (null? larg)
	  prev-args-bc
	  (let* ((arg (car larg))
		 (reste (cdr larg))
		 (calc-arg-bc (bcompile arg #f lib?)))
	    (loop reste (list calc-arg-bc prev-args-bc)))))))

(define bcompile-call-C
  (lambda (node tail? lib?)
    (let ((cprim-no (cdr (get-val (get-op node)))))
      (if (= cprim-no apply1-cprim-no)
	  (bcompile-call-I node tail? lib?)     ; Le cas apply
	  (let* ((larg (get-larg node))
		 (calc-args-bc (bcompile-calc-args larg lib?))
		 (apply-bc (list (- 255 cprim-no)))
		 (call-bc (list calc-args-bc apply-bc)))
	    (if tail?
		(list 15 call-bc 14)
		(list 25 call-bc 26)))))))

(define bcompile-call-Fi
  (lambda (node tail? lib?)
    (let* ((op (get-op node))
	   (larg (get-larg node))
	   (calc-args-bc (bcompile-calc-args larg lib?))
	   (fdesc (get-fdesc op))
	   (make-frame-bc (bcompile-make-frame fdesc))
	   (body (get-body op))
	   (body-bc (bcompile body tail? lib?)))
      (if tail?
	  (list 15 calc-args-bc make-frame-bc body-bc)
	  (list 25 calc-args-bc make-frame-bc body-bc 26 35)))))

(define bcompile-call-I
  (lambda (node tail? lib?)
    (let ((op (get-op node)))
      (if (and (ref-node? op) (get-glob? op))
	  (let* ((larg (get-larg node))
		 (calc-args-bc (bcompile-calc-args larg lib?))
		 (var-desc (vector-ref glob-v (get-loc op)))
		 (phys-no (if lib? (get-libno var-desc) (get-srcno var-desc))))
	    (if (< phys-no 256)
		(if tail?
		    (list 15 calc-args-bc 52 phys-no)
		    (list 45 calc-args-bc 54 phys-no))
		(if tail?
		    (list 15 calc-args-bc 53 (bcompile-no phys-no))
		    (list 45 calc-args-bc 55 (bcompile-no phys-no)))))
	  (let* ((larg (get-larg node))
		 (allarg (cons op larg))
		 (allarg-bc (bcompile-calc-args allarg lib?)))
	    (if tail?
		(list 15 allarg-bc 17)
		(list 45 allarg-bc 46)))))))

(define bcompile-call
  (lambda (node tail? lib?)
    (let ((op (get-op node)))
      (cond ((ref-node? op)
	     (let ((val (get-val op)))
	       (if (and val (eq? (car val) 'cprim))
		   (bcompile-call-C node tail? lib?)
		   (bcompile-call-I node tail? lib?))))
	    ((lambda-node? op)
	     (bcompile-call-Fi node tail? lib?))
	    (else
	     (bcompile-call-I node tail? lib?))))))

(define bcompile
  (let ((action-v
	 (vector
	  bcompile-cte
	  bcompile-ref
	  bcompile-lambda
	  bcompile-if
	  bcompile-set!
	  bcompile-begin
	  bcompile-def
	  bcompile-call)))
    (lambda (node tail? lib?)
      ((vector-ref action-v (node-type node)) node tail? lib?))))

(define bcompile-program
  (lambda ()
    (map (lambda (ass) (set-label! (cdr ass) (make-label)))
	 req-clos-nodes)
    (let* ((source-bc (map (lambda (node) (list (bcompile node #f #f) 51))
			   lnode))
	   (fin-bc (list 24))
	   (lib-bc (map (lambda (ass)
			  (let ((node (cdr ass)))
			    (list (bcompile-label-def (get-label node))
				  (bcompile-closure node #t))))
			req-clos-nodes))
	   (apply-hook-bc (list 17)))
      (list source-bc fin-bc lib-bc apply-hook-bc))))

(define flatten-bytecode
  (lambda (hierarcode)
    (let loop ((h hierarcode) (rest '()))
      (if (pair? h)
	  (loop (car h) (loop (cdr h) rest))
	  (if (null? h)
	      rest
	      (cons h rest))))))

(define link-bytecode
  (lambda (flat-reloc-bc)
    (let loop ((bc flat-reloc-bc) (pos 0))
      (if (not (null? bc))
	  (let ((head (car bc)))
	    (cond ((number? head)
		   (loop (cdr bc) (+ pos 1)))
		  ((eq? head 'ref)
		   (loop (cddr bc) (+ pos 2)))
		  (else ; (eq? head 'def)
		   (let ((label-no (cadr bc)))
		     (vector-set! label-v label-no pos)
		     (loop (cddr bc) pos)))))))
    (let loop ((bc flat-reloc-bc))
      (if (null? bc)
	  '()
	  (let ((head (car bc)))
	    (cond ((number? head)
		   (cons head (loop (cdr bc))))
		  ((eq? head 'ref)
		   (let* ((label-no (cadr bc))
			  (pos (vector-ref label-v label-no)))
		     (append (bcompile-no pos) (loop (cddr bc)))))
		  (else ; (eq? head 'def)
		   (loop (cddr bc)))))))))




; Codage de la valeur initiale des variables globales

(define glob-var-init-codes #f)

(define code-init
  (lambda (init)
    (cond ((not init)
	   -1)
	  ((eq? (car init) 'cprim)
	   (- -2 (cdr init)))
	  (else ; (eq? (car init) 'clos)
	   (let* ((lambda-node (cdr init))
		  (label-no (get-label lambda-node)))
	     (vector-ref label-v label-no))))))

(define code-glob-inits
  (lambda ()
    (let loop ((var-no (- glob-counter 1)) (codes '()))
      (if (< var-no 0)
	  codes
	  (let* ((var-desc (vector-ref glob-v var-no))
		 (var-init (get-init var-desc))
		 (init-code (code-init var-init))
		 (newcodes (if (= (get-libno var-desc)
				  (get-srcno var-desc))
			       (cons init-code codes)
			       (cons init-code (cons init-code codes)))))
	    (loop (- var-no 1) newcodes))))))




; Impression des resultats

(define byte-strings
  (vector
   "   0" "   1" "   2" "   3" "   4" "   5" "   6" "   7" "   8" "   9"
   "  10" "  11" "  12" "  13" "  14" "  15" "  16" "  17" "  18" "  19"
   "  20" "  21" "  22" "  23" "  24" "  25" "  26" "  27" "  28" "  29"
   "  30" "  31" "  32" "  33" "  34" "  35" "  36" "  37" "  38" "  39"
   "  40" "  41" "  42" "  43" "  44" "  45" "  46" "  47" "  48" "  49"
   "  50" "  51" "  52" "  53" "  54" "  55" "  56" "  57" "  58" "  59"
   "  60" "  61" "  62" "  63" "  64" "  65" "  66" "  67" "  68" "  69"
   "  70" "  71" "  72" "  73" "  74" "  75" "  76" "  77" "  78" "  79"
   "  80" "  81" "  82" "  83" "  84" "  85" "  86" "  87" "  88" "  89"
   "  90" "  91" "  92" "  93" "  94" "  95" "  96" "  97" "  98" "  99"
   " 100" " 101" " 102" " 103" " 104" " 105" " 106" " 107" " 108" " 109"
   " 110" " 111" " 112" " 113" " 114" " 115" " 116" " 117" " 118" " 119"
   " 120" " 121" " 122" " 123" " 124" " 125" " 126" " 127" " 128" " 129"
   " 130" " 131" " 132" " 133" " 134" " 135" " 136" " 137" " 138" " 139"
   " 140" " 141" " 142" " 143" " 144" " 145" " 146" " 147" " 148" " 149"
   " 150" " 151" " 152" " 153" " 154" " 155" " 156" " 157" " 158" " 159"
   " 160" " 161" " 162" " 163" " 164" " 165" " 166" " 167" " 168" " 169"
   " 170" " 171" " 172" " 173" " 174" " 175" " 176" " 177" " 178" " 179"
   " 180" " 181" " 182" " 183" " 184" " 185" " 186" " 187" " 188" " 189"
   " 190" " 191" " 192" " 193" " 194" " 195" " 196" " 197" " 198" " 199"
   " 200" " 201" " 202" " 203" " 204" " 205" " 206" " 207" " 208" " 209"
   " 210" " 211" " 212" " 213" " 214" " 215" " 216" " 217" " 218" " 219"
   " 220" " 221" " 222" " 223" " 224" " 225" " 226" " 227" " 228" " 229"
   " 230" " 231" " 232" " 233" " 234" " 235" " 236" " 237" " 238" " 239"
   " 240" " 241" " 242" " 243" " 244" " 245" " 246" " 247" " 248" " 249"
   " 250" " 251" " 252" " 253" " 254" " 255"))

(define write-bytecode
  (lambda (bc port)
    (display "int bytecode_len = " port)
    (let ((len (length bc)))
      (write len port)
      (if (> len 32768)
	  (begin
	    (display "Warning: bytecode too long.")
	    (newline))))
    (display ";" port)
    (newline port)
    (display "unsigned char bytecode[] = {" port)
    (let ((virgule ""))
      (let loop ((bc bc) (mod 0))
	(if (not (null? bc))
	    (begin
	      (display virgule port)
	      (set! virgule ",")
	      (if (= mod 0)
		  (begin
		    (newline port)
		    (display "       " port)
		    (set! mod -12)))
	      (display (vector-ref byte-strings (car bc)) port)
	      (loop (cdr bc) (+ mod 1))))))
    (display "};" port)
    (newline port)))

(define write-const-desc
  (lambda (cd port)
    (let ((cd (map char->integer (string->list cd))))
      (display "int const_desc_len = " port)
      (write (length cd) port)
      (display ";" port)
      (newline port)
      (display "unsigned char const_desc[] = {" port)
      (let ((virgule ""))
	(let loop ((cd cd) (mod 0))
	  (if (not (null? cd))
	      (begin
		(display virgule port)
		(set! virgule ",")
		(if (= mod 0)
		    (begin
		      (newline port)
		      (display "       " port)
		      (set! mod -12)))
		(display (vector-ref byte-strings (car cd)) port)
		(loop (cdr cd) (+ mod 1))))))
      (display "};" port)
      (newline port))))

(define pretty-signed-int
  (lambda (int)
    (let* ((sint (number->string int))
	   (lpadding (- 6 (string-length sint)))
	   (padding (substring "        " 0 lpadding)))
      (string-append padding sint))))

(define write-glob-init-codes
  (lambda (glob-var-init-codes port)
    (display "int nb_scm_globs = " port)
    (write (length glob-var-init-codes) port)
    (display ";" port)
    (newline port)
    (display "int scm_globs[] = {" port)
    (let ((virgule ""))
      (let loop ((gi glob-var-init-codes) (mod 0))
	(if (not (null? gi))
	    (begin
	      (display virgule port)
	      (set! virgule ",")
	      (if (= mod 0)
		  (begin
		    (newline port)
		    (display "       " port)
		    (set! mod -8)))
	      (display (pretty-signed-int (car gi)) port)
	      (loop (cdr gi) (+ mod 1))))))
    (display "};" port)
    (newline port)))

(define write-output
  (lambda (final-program-bytecode
	   const-desc-string
	   glob-var-init-codes
	   nameout)
    (let ((port (open-output-file nameout)))
      (write-bytecode        final-program-bytecode port) (newline port)
      (write-const-desc      const-desc-string      port) (newline port)
      (write-glob-init-codes glob-var-init-codes    port)
      (close-output-port port))))




; Programme principal

(define byte-compile
  (lambda (namein nameout)
    (init-glob-vars)
    (let* ((source (read-source namein))
	   (source-symbols (find-all-symbols source))
	   (uniq-pref (find-uniq-prefix source-symbols)))
      (set! gen-sym-pref uniq-pref)
      (set! safe-name-memv         (gen-sym))
      (set! safe-name-make-promise (gen-sym))
      (set! safe-name-list->vector (gen-sym))
      (set! safe-name-list         (gen-sym))
      (set! safe-name-append2      (gen-sym))
      (set! safe-name-cons         (gen-sym))
      (let* ((source++
	      (append
	       (list
		(list 'define safe-name-memv         'memv)
		(list 'define safe-name-make-promise 'make-promise)
		(list 'define safe-name-list->vector 'list->vector)
		(list 'define safe-name-list         'list)
		(list 'define safe-name-append2      'append2)
		(list 'define safe-name-cons         'cons)
		'(install-const))
	       source))
	     (simple (map trans-sub source++)))
	(set! lnode (map exp->node simple))
	(let* ((llglob (map extract-glob-names lnode))
	       (lglob (foldr symbol-set-union '() llglob)))
	  (load-lib)
	  (set! dirreq (symbol-set-intersection lglob libpublics))
	  (grab-lib dirreq)
	  (traverse1)
	  (find-inits)
	  (traverse2)
	  (assign-phys-no)
	  (set! program-bytecode (bcompile-program))
	  (set! flat-program-bytecode (flatten-bytecode program-bytecode))
	  (set! final-program-bytecode (link-bytecode flat-program-bytecode))
	  (set! const-desc-string (code-const))
	  (set! glob-var-init-codes (code-glob-inits))
	  (write-output final-program-bytecode const-desc-string
			glob-var-init-codes nameout))))))
