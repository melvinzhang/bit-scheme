(define (read-all)
  (let ((datum (read)))
    (if (eof-object? datum) (display "EOF reached")
      (begin
        (write datum)
        (newline)
        (read-all)))))

(read-all)
