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
        ))))
