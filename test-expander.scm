(write (expand-program (list
  '(let-syntax ((x append)) ((x x)))
  '(let ((n 0))
    (let-syntax ((x (set! n (+ n 1))))
      (begin x x x n)))
  '(let-syntax ((q quote)) (q x))
  '((syntax-rules ()
     ((let ((var init) ...) . body)
      ((lambda (var ...) . body)
       init ...)))
   ((x 1) (y 2))
   (+ x y))
)))
(newline)