; Copyright (C) 1995 Danny Dube, Universite de Montreal. All rights reserved.

;
; Fonctions implantees dans le noyau. Pour savoir lesquelles
; sont visibles, voir sections plus bas
;

(peek-char                   .  0)
(read-char                   .  1)
(quit                        .  2)
(return-current-continuation .  3)
(boolean?                    .  4)
(pair?                       .  5)
(car                         .  6)
(cdr                         .  7)
(char?                       .  8)
(integer->char               .  9)
(char->integer               . 10)
(string?                     . 11)
(make-string1                . 12)
(string-length               . 13)
(string-copy                 . 14)
(symbol?                     . 15)
(symbol->string              . 16)
(string->symbol              . 17)
(number?                     . 18)
(vector?                     . 19)
(make-vector1                . 20)
(vector-length               . 21)
(procedure?                  . 22)
(write-char                  . 23)
(introspection               . 24)
(cons                        . 25)
(set-car!                    . 26)
(set-cdr!                    . 27)
(string-ref                  . 28)
(string=?                    . 29)
(cppoe2                      . 30)
(cplus2                      . 31)
(cmoins2                     . 32)
(cfois2                      . 33)
(cdivise2                    . 34)
(vector-ref                  . 35)
(apply1                      . 36)
(eq?                         . 37)
(return-there-with-this      . 38)
(string-set!                 . 39)
(vector-set!                 . 40)

#f ; Fin des definitions des primitives C

;
; Fonctions cachees de la librairie
;

(define foldl
  (lambda (binop start l)
    (if (null? l)
	start
	(foldl binop (binop start (car l)) (cdr l)))))
(define foldl1
  (lambda (binop l)
    (if (null? (cdr l))
	(car l)
	(foldl1 binop (cons (binop (car l) (cadr l))
			    (cddr l))))))
(define foldr1
  (lambda (binop l)
    (if (null? (cdr l))
	(car l)
	(binop (car l) (foldr1 binop (cdr l))))))

(define generic-member
  (lambda (releq obj list)
    (if (null? list)
	#f
	(if (releq (car list) obj)
	    list
	    (generic-member releq obj (cdr list))))))

(define generic-assoc
  (lambda (releq obj alist)
    (cond ((null? alist)
	   #f)
	  ((releq (car (car alist)) obj)
	   (car alist))
	  (else
	   (generic-assoc releq obj (cdr alist))))))

(define math=2
  (lambda (x y)
    (if (math<=2 x y) (math<=2 y x) #f)))

(define math<2
  (lambda (x y)
    (not (math<=2 y x))))

(define math>2
  (lambda (x y)
    (not (math<=2 x y))))

(define math<=2 cppoe2)

(define math>=2 (lambda (x y) (math<=2 y x)))

(define generic-compare
  (lambda (binrel l)
    (if (null? (cddr l))
	(binrel (car l) (cadr l))
	(and (binrel (car l) (cadr l))
	     (generic-compare binrel (cdr l))))))

(define max2 (lambda (x y) (if (> x y) x y)))
(define min2 (lambda (x y) (if (< x y) x y)))

(define math+2 cplus2)

(define math*2 cfois2)

(define math-2 cmoins2)

(define math/2 cdivise2)

(define math%2
  (lambda (num den)
    (math-2 num (math*2 den (math/2 num den)))))

(define mathgcd2
  (lambda (n1 n2)
    (let loop ((n1 (abs n1)) (n2 (abs n2)))
      (cond ((zero? n1) n2)
	    ((zero? n2) n1)
	    (else
	     (let ((grand (max n1 n2))
		   (petit (min n1 n2)))
	       (loop petit (modulo grand petit))))))))

(define mathlcm2
  (lambda (n1 n2)
    (cond ((zero? n1) (abs n2))
	  ((zero? n2) (abs n1))
	  (else
	   (let ((n1 (abs n1))
		 (n2 (abs n2)))
	     (/ (* n1 n2) (mathgcd2 n1 n2)))))))

(define string-compare
  (lambda (rel<? rel=? s1 s2)
    (let* ((len1 (string-length s1))
	   (len2 (string-length s2))
	   (len (min len1 len2)))
      (let loop ((pos 0))
	(if (< pos len)
	    (let* ((c1 (string-ref s1 pos))
		   (c2 (string-ref s2 pos)))
	      (cond ((rel<? c1 c2)
		     -1)
		    ((rel=? c1 c2)
		     (loop (+ pos 1)))
		    (else
		     1)))
	    (cond ((< len1 len2)
		   -1)
		  ((= len1 len2)
		   0)
		  (else
		   1)))))))

(define map1
  (lambda (f l)
    (if (null? l)
	l
	(cons (f (car l)) (map1 f (cdr l))))))

(define write-many-chars
  (lambda l
    (for-each write-char l)))

(define write-cdr
  (lambda (d parent)
    (cond ((eq? d '())
	   (write-char #\)))
	  ((pair? d)
	   (write-char #\space)
	   (parent (car d))
	   (write-cdr (cdr d) parent))
	  (else
	   (write-many-chars #\space #\. #\space)
	   (parent d)
	   (write-char #\))))))

(define write-vector
  (lambda (d parent)
    (let ((len (vector-length d)))
      (write-many-chars #\# #\()
      (if (> len 0)
	  (begin
	    (parent (vector-ref d 0))
	    (let loop ((pos 1))
	      (if (< pos len)
		  (begin
		    (write-char #\space)
		    (parent (vector-ref d pos))
		    (loop (+ pos 1)))))))
      (write-char #\)))))

(define make-byte-reader
  (lambda (s)
    (let ((pos 0))
      (lambda ()
	(let ((c (string-ref s pos)))
	  (set! pos (+ pos 1))
	  c)))))
(define make-number-reader
  (lambda (read-const-byte)
    (lambda ()
      (let* ((msc (read-const-byte))
	     (lsc (read-const-byte))
	     (msb (char->integer msc))
	     (lsb (char->integer lsc)))
	(+ (* msb 256) lsb)))))
(define read-const-desc
  (lambda (const-v pos read-const-byte read-const-number)
    (let ((type (read-const-byte)))
      (cond
       ((char=? type #\0)  ; EMPTY
	'())
       ((char=? type #\1)  ; PAIR
	(let* ((incar (vector-ref const-v (read-const-number)))
	       (incdr (vector-ref const-v (read-const-number))))
	  (cons incar incdr)))
       ((char=? type #\2)  ; BOOLEAN
	(char=? (read-const-byte) #\t))
       ((char=? type #\3)  ; CHAR
	(read-const-byte))
       ((char=? type #\4)  ; STRING
	(let* ((len (read-const-number))
	       (s (make-string len)))
	  (let loop ((pos 0))
	    (if (< pos len)
		(begin
		  (string-set! s pos (read-const-byte))
		  (loop (+ pos 1)))))
	  s))
       ((char=? type #\5)  ; SYMBOL
	(string->symbol (vector-ref const-v (read-const-number))))
       ((char=? type #\6)  ; NUMBER
	(let* ((sign (read-const-byte))
	       (valabs (read-const-number)))
	  (if (char=? sign #\+)
	      valabs
	      (- valabs))))
       ((char=? type #\7)  ; VECTOR
	(let* ((len (read-const-number))
	       (v (make-vector len)))
	  (let loop ((pos 0))
	    (if (< pos len)
		(begin
		  (vector-set! v pos (vector-ref const-v (read-const-number)))
		  (loop (+ pos 1)))))
	  v))))))
(define extract-top-const
  (lambda (const-v read-const-number)
    (let* ((nbtop (read-const-number))
	   (top-v (make-vector nbtop)))
      (let loop ((pos 0))
	(if (< pos nbtop)
	    (begin
	      (vector-set! top-v pos (vector-ref const-v (read-const-number)))
	      (loop (+ pos 1)))))
      top-v)))

#f ; Fin des definitions des fonctions internes

;
; Les fonctions non-standard mais visibles tout
; de meme pour les programmes compiles
;

(define append2
  (lambda (l1 l2)
    (if (null? l1)
	l2
	(let ((tete (cons (car l1) l2)))
	  (let loop ((cur tete) (l1 (cdr l1)))
	    (if (null? l1)
		tete
		(begin
		  (set-cdr! cur (cons (car l1) l2))
		  (loop (cdr cur) (cdr l1)))))))))

quit

(define make-promise
  (lambda (proc)
    (let ((result-ready? #f)
	  (result #f))
      (lambda ()
	(if result-ready?
	    result
	    (let ((x (proc)))
	      (if result-ready?
		  result
		  (begin (set! result-ready? #t)
			 (set! result x)
			 result))))))))

; Note tres importante: cette fonction sert a reconstituer les constantes
; du programme avant le debut de son execution. Toute fonction appelee
; durant l'execution de celle-ci ne doit pas comporter de constantes etant
; donne qu'elles ne sont pas encore baties.
(define install-const
  (lambda ()
    (let* ((const-string (introspection #f))  ; Porte secrete!
	   (read-const-byte (make-byte-reader const-string))
	   (read-const-number (make-number-reader read-const-byte))
	   (nbconst (read-const-number))
	   (const-v (make-vector nbconst)))
      (let loop ((pos 0))
	(if (< pos nbconst)
	    (begin
	      (vector-set! const-v
			   pos
			   (read-const-desc const-v
					    pos
					    read-const-byte
					    read-const-number))
	      (loop (+ pos 1)))))
      (let ((top-v (extract-top-const const-v read-const-number)))
	(introspection top-v)))))             ; Porte secrete!

#f ; Fin des definitions des fonctions non-standard visibles

;
; Debut des fonctions Scheme standard de la librairie
;

; 6.1
(define not (lambda (x) (if x #f #t)))
boolean?

; 6.2
(define eqv?
  (lambda (d1 d2)
    (cond ((and (number? d1) (number? d2))
	   (= d1 d2))
	  ((and (char? d1) (char? d2))
	   (char=? d1 d2))
	  (else
	   (eq? d1 d2)))))
eq?
(define equal?
  (lambda (d1 d2)
    (cond ((eqv? d1 d2)
	   #t)
	  ((and (pair? d1) (pair? d2))
	   (and (equal? (car d1) (car d2)) (equal? (cdr d1) (cdr d2))))
	  ((and (vector? d1) (vector? d2))
	   (let ((len (vector-length d1)))
	     (if (not (= len (vector-length d2)))
		 #f
		 (let loop ((pos 0))
		   (cond ((>= pos len)
			  #t)
			 ((equal? (vector-ref d1 pos) (vector-ref d2 pos))
			  (loop (+ pos 1)))
			 (else
			  #f))))))
	  ((and (string? d1) (string? d2))
	   (string=? d1 d2))
	  (else
	   #f))))

; 6.3
pair?
cons
car
cdr
set-car!
set-cdr!
(define caar (lambda (p) (car (car p))))
(define cadr (lambda (p) (car (cdr p))))
(define cdar (lambda (p) (cdr (car p))))
(define cddr (lambda (p) (cdr (cdr p))))
(define caaar (lambda (p) (caar (car p))))
(define caadr (lambda (p) (caar (cdr p))))
(define cadar (lambda (p) (cadr (car p))))
(define caddr (lambda (p) (cadr (cdr p))))
(define cdaar (lambda (p) (cdar (car p))))
(define cdadr (lambda (p) (cdar (cdr p))))
(define cddar (lambda (p) (cddr (car p))))
(define cdddr (lambda (p) (cddr (cdr p))))
(define caaaar (lambda (p) (caaar (car p))))
(define caaadr (lambda (p) (caaar (cdr p))))
(define caadar (lambda (p) (caadr (car p))))
(define caaddr (lambda (p) (caadr (cdr p))))
(define cadaar (lambda (p) (cadar (car p))))
(define cadadr (lambda (p) (cadar (cdr p))))
(define caddar (lambda (p) (caddr (car p))))
(define cadddr (lambda (p) (caddr (cdr p))))
(define cdaaar (lambda (p) (cdaar (car p))))
(define cdaadr (lambda (p) (cdaar (cdr p))))
(define cdadar (lambda (p) (cdadr (car p))))
(define cdaddr (lambda (p) (cdadr (cdr p))))
(define cddaar (lambda (p) (cddar (car p))))
(define cddadr (lambda (p) (cddar (cdr p))))
(define cdddar (lambda (p) (cdddr (car p))))
(define cddddr (lambda (p) (cdddr (cdr p))))
(define null?
  (lambda (x) (eq? x '())))
(define list?
  (lambda (l)
    (cond ((null? l)
	   #t)
	  ((not (pair? l))
	   #f)
	  (else
	   (let loop ((slow l) (fast (cdr l)) (phase 2))
	     (cond ((null? fast)
		    #t)
		   ((not (pair? fast))
		    #f)
		   ((eq? slow fast)
		    #f)
		   ((= phase 1)
		    (loop slow (cdr fast) 2))
		   (else
		    (loop (cdr slow) (cdr fast) 1))))))))
(define list (lambda l l))
(define length
  (lambda (l)
    (let loop ((l l) (len 0))
      (if (null? l)
	  len
	  (loop (cdr l) (+ len 1))))))
(define append
  (lambda ll
    (foldr1 append2 (cons '() ll))))
(define reverse
  (lambda (l)
    (let loop ((l l) (rl '()))
      (if (null? l)
	  rl
	  (loop (cdr l) (cons (car l) rl))))))
(define list-tail
  (lambda (l pos)
    (if (= pos 0)
	l
	(list-tail (cdr l) (- pos 1)))))
(define list-ref (lambda (l pos) (car (list-tail l pos))))
(define memq
  (lambda (obj list)
    (generic-member eq? obj list)))
(define memv
  (lambda (obj list)
    (generic-member eqv? obj list)))
(define member
  (lambda (obj list)
    (generic-member equal? obj list)))
(define assq (lambda (obj alist) (generic-assoc eq? obj alist)))
(define assv (lambda (obj alist) (generic-assoc eqv? obj alist)))
(define assoc (lambda (obj alist) (generic-assoc equal? obj alist)))

; 6.4
symbol?
symbol->string
string->symbol

; 6.5
number?
(define complex? number?)
(define real? number?)
(define rational? number?)
(define integer? number?)
(define exact? (lambda (n) #t))
(define inexact? (lambda (n) #f))
(define =  (lambda l (generic-compare math=2  l)))
(define <  (lambda l (generic-compare math<2  l)))
(define >  (lambda l (generic-compare math>2  l)))
(define <= (lambda l (generic-compare math<=2 l)))
(define >= (lambda l (generic-compare math>=2 l)))
(define zero? (lambda (n) (= n 0)))
(define positive? (lambda (n) (> n 0)))
(define negative? (lambda (n) (< n 0)))
(define odd? (lambda (n) (= (math%2 (abs n) 2) 1)))
(define even? (lambda (n) (= (math%2 (abs n) 2) 0)))
(define max (lambda l (foldl1 max2 l)))
(define min (lambda l (foldl1 min2 l)))
(define + (lambda l (foldl math+2 0 l)))
(define * (lambda l (foldl math*2 1 l)))
(define - (lambda l (if (null? (cdr l)) (math-2 0 (car l)) (foldl1 math-2 l))))
(define /
  (lambda l (if (null? (cdr l)) (quotient 1 (car l)) (foldl1 quotient l))))
(define abs (lambda (n) (if (negative? n) (- n) n)))
(define quotient
  (lambda (n d)
    (if (= d 0)
	1
	(if (>= n 0)
	    (if (> d 0)
		(math/2 n d)
		(- (math/2 n (- d))))
	    (if (> d 0)
		(- (math/2 (- n) d))
		(math/2 (- n) (- d)))))))
(define remainder (lambda (n d) (- n (* d (quotient n d)))))
(define modulo
  (lambda (n d)
    (if (= d 0)
	n
	(if (> d 0)
	    (if (>= n 0)
		(remainder n d)
		(remainder (+ (remainder n d) d) d))
	    (- (modulo (- n) (- d)))))))
(define gcd (lambda l (foldl mathgcd2 0 l)))
(define lcm (lambda l (foldl mathlcm2 1 l)))
(define numerator   (lambda (q) q))
(define denominator (lambda (q) 1))
(define floor numerator)
(define ceiling numerator)
(define truncate numerator)
(define round numerator)
(define rationalize (lambda (x y) x))
(define sqrt
  (lambda (x)
    (cond ((not (positive? x))
	   0)
	  ((= x 1)
	   1)
	  (else
	   (let loop ((sous 1) (sur x))
	     (if (<= (- sur sous) 1)
		 sous
		 (let* ((new (/ (+ sous sur) 2)))
		   (if (<= (* new new) x)
		       (loop new sur)
		       (loop sous new)))))))))
(define expt
  (lambda (base exp)
    (if (not (positive? exp))
	1
	(let* ((facteur (if (odd? exp) base 1))
	       (reste (expt (* base base) (/ exp 2))))
	  (* facteur reste)))))
(define exact->inexact (lambda (z) z))
(define inexact->exact (lambda (z) z))
(define number->string
  (lambda (n . lradix)
    (let* ((radix (if (null? lradix) 10 (car lradix)))
	   (negative (negative? n))
	   (absn (abs n)))
      (if (= n 0)
	  (string-copy "0")
	  (letrec ((decomp (lambda (n digits)
			     (if (= n 0)
				 digits
				 (decomp (/ n radix)
					 (cons (modulo n radix) digits))))))
	    (let* ((nd->ad (lambda (n)
			     (if (< n 10)
				 (+ n (char->integer #\0))
				 (+ (- n 10) (char->integer #\a)))))
		   (digits (decomp absn '()))
		   (adigits (map nd->ad digits))
		   (cdigits (map integer->char adigits))
		   (signedchars (if negative
				    (cons #\- cdigits)
				    cdigits)))
	      (list->string signedchars)))))))
(define string->number
  (lambda (str . lradix)
    (let* ((radix (if (null? lradix) 10 (car lradix)))
	   (maxnum (if (<= radix 10)
		       (integer->char (+ (- radix 1) (char->integer #\0)))
		       #\9))
	   (len (string-length str)))
      (letrec ((checkdigit
		(lambda (d)
		  (if (<= radix 10)
		      (and (char<=? #\0 d) (char<=? d maxnum))
		      (or (and (char<=? #\0 d) (char<=? d maxnum))
			  (and (char<=? #\a (char-downcase d))
			       (char<=? (char-downcase d) #\f))))))
	       (checksyntax
		(lambda (min pos)
		  (if (>= pos len)
		      (>= pos min)
		      (let ((d (string-ref str pos)))
			(cond ((checkdigit d)
			       (checksyntax min (+ pos 1)))
			      ((or (char=? d #\+) (char=? d #\-))
			       (and (= pos 0) (checksyntax 2 1)))
			      (else #f))))))
	       (recomp (lambda (acc digits)
			 (if (null? digits)
			     acc
			     (recomp (+ (* acc radix) (car digits))
				     (cdr digits)))))
	       (cd->nd (lambda (c)
			 (if (char-numeric? c)
			     (- (char->integer c) (char->integer #\0))
			     (+ (- (char->integer (char-downcase c))
				   (char->integer #\a))
				10)))))
	(and (checksyntax 1 0)
	     (let* ((signedchars (string->list str))
		    (negative (char=? (car signedchars) #\-))
		    (positive (char=? (car signedchars) #\+))
		    (cdigits (if (or negative positive)
				 (cdr signedchars)
				 signedchars))
		    (digits (map cd->nd cdigits))
		    (absn (recomp 0 digits)))
	       (if negative (- absn) absn)))))))

; 6.6
char?
(define char=? (lambda (c1 c2) (= (char->integer c1) (char->integer c2))))
(define char<? (lambda (c1 c2) (not (char<=? c2 c1))))
(define char>? (lambda (c1 c2) (not (char<=? c1 c2))))
(define char<=? (lambda (c1 c2) (<= (char->integer c1) (char->integer c2))))
(define char>=? (lambda (c1 c2) (char<=? c2 c1)))
(define char-ci=?
  (lambda (c1 c2) (char=? (char-downcase c1) (char-downcase c2))))
(define char-ci<?
  (lambda (c1 c2) (char<? (char-downcase c1) (char-downcase c2))))
(define char-ci>?
  (lambda (c1 c2) (char>? (char-downcase c1) (char-downcase c2))))
(define char-ci<=?
  (lambda (c1 c2) (char<=? (char-downcase c1) (char-downcase c2))))
(define char-ci>=?
  (lambda (c1 c2) (char>=? (char-downcase c1) (char-downcase c2))))
(define char-alphabetic?
  (lambda (c) (and (char-ci<=? #\a c) (char-ci<=? c #\z))))
(define char-numeric? (lambda (c) (and (char<=? #\0 c) (char<=? c #\9))))
(define char-whitespace?
  (lambda (c)
    (or (char=? c #\space)
	(char=? c (integer->char 9))     ; Tab
	(char=? c #\newline)
	(char=? c (integer->char 12))    ; FF
	(char=? c (integer->char 13))))) ; CR
(define char-upper-case? (lambda (c) (and (char<=? #\A c) (char<=? c #\Z))))
(define char-lower-case? (lambda (c) (and (char<=? #\a c) (char<=? c #\z))))
char->integer
integer->char
(define char-upcase
  (lambda (c)
    (if (char-lower-case? c)
	(integer->char (+ (char->integer c)
			  (- (char->integer #\A) (char->integer #\a))))
	c)))
(define char-downcase
  (lambda (c)
    (if (char-upper-case? c)
	(integer->char (+ (char->integer c)
			  (- (char->integer #\a) (char->integer #\A))))
	c)))

; 6.7
string?
(define make-string
  (lambda (len . lfill)
    (let ((str (make-string1 len)))
      (if (not (null? lfill))
	  (string-fill! str (car lfill)))
      str)))
(define string (lambda l (list->string l)))
string-length
string-ref
string-set!
string=?
(define string<?
  (lambda (s1 s2) (<  (string-compare char<? char=? s1 s2) 0)))
(define string>?
  (lambda (s1 s2) (>  (string-compare char<? char=? s1 s2) 0)))
(define string<=?
  (lambda (s1 s2) (<= (string-compare char<? char=? s1 s2) 0)))
(define string>=?
  (lambda (s1 s2) (>= (string-compare char<? char=? s1 s2) 0)))
(define string-ci=?
  (lambda (s1 s2) (=  (string-compare char-ci<? char-ci=? s1 s2) 0)))
(define string-ci<?
  (lambda (s1 s2) (<  (string-compare char-ci<? char-ci=? s1 s2) 0)))
(define string-ci>?
  (lambda (s1 s2) (>  (string-compare char-ci<? char-ci=? s1 s2) 0)))
(define string-ci<=?
  (lambda (s1 s2) (<= (string-compare char-ci<? char-ci=? s1 s2) 0)))
(define string-ci>=?
  (lambda (s1 s2) (>= (string-compare char-ci<? char-ci=? s1 s2) 0)))
(define substring
  (lambda (str start end)
    (let* ((len (- end start))
	   (newstr (make-string len)))
      (let loop ((pos 0))
	(if (< pos len)
	    (begin
	      (string-set! newstr pos (string-ref str (+ start pos)))
	      (loop (+ pos 1)))))
      newstr)))
(define string-append
  (lambda ls
    (let* ((llen (map string-length ls))
	   (totlen (foldl + 0 llen))
	   (newstring (make-string totlen))
	   (iter (lambda (iter ls llen from to)
		   (if (< to totlen)
		       (if (< from (car llen))
			   (begin
			     (string-set! newstring
					  to
					  (string-ref (car ls) from))
			     (iter iter ls llen (+ from 1) (+ to 1)))
			   (iter iter (cdr ls) (cdr llen) 0 to))))))
      (iter iter ls llen 0 0)
      newstring)))
(define string->list
  (lambda (str)
    (let loop ((pos (- (string-length str) 1)) (l '()))
      (if (< pos 0)
	  l
	  (loop (- pos 1) (cons (string-ref str pos) l))))))
(define list->string
  (lambda (l)
    (let* ((len (length l))
	   (newstring (make-string1 len))
	   (iter (lambda (iter l to)
		   (if (< to len)
		       (begin
			 (string-set! newstring to (car l))
			 (iter iter (cdr l) (+ to 1)))))))
      (iter iter l 0)
      newstring)))
string-copy
(define string-fill!
  (lambda (str fill)
    (let loop ((pos (- (string-length str) 1)))
      (if (>= pos 0)
	  (begin
	    (string-set! str pos fill)
	    (loop (- pos 1)))))))

; 6.8
vector?
(define make-vector
  (lambda (len . lfill)
    (let ((v (make-vector1 len)))
      (if (not (null? lfill))
	  (vector-fill! v (car lfill)))
      v)))
(define vector (lambda l (list->vector l)))
vector-length
vector-ref
vector-set!
(define vector->list
  (lambda (v)
    (let loop ((pos (- (vector-length v) 1)) (l '()))
      (if (< pos 0)
	  l
	  (loop (- pos 1) (cons (vector-ref v pos) l))))))
(define list->vector
  (lambda (l)
    (let* ((len (length l))
	   (v (make-vector len)))
      (let loop ((l l) (pos 0))
	(if (not (null? l))
	    (begin
	      (vector-set! v pos (car l))
	      (loop (cdr l) (+ pos 1)))))
      v)))
(define vector-fill!
  (lambda (v fill)
    (let loop ((pos (- (vector-length v) 1)))
      (if (>= pos 0)
	  (begin
	    (vector-set! v pos fill)
	    (loop (- pos 1)))))))

; 6.9
procedure?
(define apply
  (lambda (proc . llargs)
    (let ((largs (if (null? (cdr llargs))
		     (car llargs)
		     (foldr1 cons llargs))))
      (apply1 proc largs))))
(define map
  (lambda (proc . ll)
    (if (null? (car ll))
	'()
	(let ((tetes (map1 car ll))
	      (queues (map1 cdr ll)))
	  (cons (apply proc tetes)
		(apply map (cons proc queues)))))))
(define for-each
  (lambda (proc . ll)
    (if (null? (car ll))
	#f
	(let* ((tetes (map car ll))
	       (queues (map cdr ll)))
	  (apply proc tetes)
	  (apply for-each (cons proc queues))))))
(define force (lambda (promise) (promise)))
(define call-with-current-continuation
  (lambda (proc)
    (let ((cc (return-current-continuation)))
      (if (vector? cc)
	  (vector-ref cc 0)
	  (let ((escape-proc (lambda (val)
			       (let ((v (vector val)))
				 (return-there-with-this cc v)))))
	    (proc escape-proc))))))
(define call/cc call-with-current-continuation)

; 6.10
read-char
peek-char
(define eof-object? (lambda (ch) (and (char? ch) (= (char->integer ch) 255))))
(define write
  (lambda (d)
    (cond ((eq? d #f)
	   (write-many-chars #\# #\f))
	  ((eq? d #t)
	   (write-many-chars #\# #\t))
	  ((symbol? d)
	   (apply write-many-chars (string->list (symbol->string d))))
	  ((eqv? d #\space)
	   (write-many-chars #\# #\\ #\s #\p #\a #\c #\e))
	  ((eqv? d #\newline)
	   (write-many-chars #\# #\\ #\n #\e #\w #\l #\i #\n #\e))
	  ((eqv? d #\tab)
	   (write-many-chars #\# #\\ #\t #\a #\b))
	  ((char? d)
	   (write-many-chars #\# #\\ d))
	  ((vector? d)
	   (write-vector d write))
	  ((pair? d)
	   (write-char #\()
	   (write (car d))
	   (write-cdr (cdr d) write))
	  ((number? d)
	   (apply write-many-chars (string->list (number->string d))))
	  ((string? d)
	   (write-char #\")
	   (let ((len (string-length d)))
	     (let loop ((pos 0))
	       (if (< pos len)
		   (let ((c (string-ref d pos)))
		     (cond 
               ((char=? c #\") (write-many-chars #\\ #\") (loop (+ pos 1)))
			   ((char=? c #\\) (write-many-chars #\\ #\\) (loop (+ pos 1)))
			   (else (write-char c) (loop (+ pos 1))))))))
	   (write-char #\"))
	  ((procedure? d)
	   (write-many-chars #\# #\< #\p #\r #\o #\c #\e #\d #\u #\r #\e #\>))
	  ((null? d)
	   (write-many-chars #\( #\)))
	  (else
	   #f))))
(define display
  (lambda (d)
    (cond ((char? d)
	   (write-char d))
	  ((vector? d)
	   (write-vector d display))
	  ((pair? d)
	   (write-char #\()
	   (display (car d))
	   (write-cdr (cdr d) display))
	  ((string? d)
	   (apply write-many-chars (string->list d)))
	  (else
	   (write d)))))
(define newline (lambda () (write-char #\newline)))
write-char

#f ; Fin des definitions des fonctions standard
