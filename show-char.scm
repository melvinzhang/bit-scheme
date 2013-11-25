(define (loop) 
  (let ((ch (read-char)))
    (if (eof-object? ch) #f
      (begin
        (display "char: ")
        (write ch)
        (display " ")
        (display "int: ")
        (write (char->integer ch))
        (newline)
        (loop)))))

(loop)
