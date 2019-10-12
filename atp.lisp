#!/usr/bin/clisp

(in-package :cl-user)

(defpackage :atp
  (:use :cl))

(in-package :atp)

                                        ; Utils
(defmacro slet (bindings &body body)
  (let* ((bind (car bindings))
         (varlst (butlast bind))
         (vals (car (last bind)))
         (leftover (cdr bindings)))
    (if leftover
        `(multiple-value-bind ,varlst ,vals (slet ,leftover ,@body))
        `(multiple-value-bind ,varlst ,vals ,@body))))

(defmacro -> (val &body body)
  (let ((f (car body))
        (leftover (cdr body)))
    (if f
        `(-> ,`(funcall ,f ,val) ,@leftover)
        val)))

(defmacro lm (sym &body body)
  `(lambda (,sym) ,@body))

(defun str->chars (str)
  (loop :for c :across str :collect c))

(defun chars->str (chars)
  (concatenate 'string chars))

(defun split-at (lst pred)
  (if (null lst)
      (values nil nil nil)
      (if (funcall pred (car lst))
          (values nil (car lst) (cdr lst))
          (slet ((head target tail (split-at (cdr lst) pred)))
            (values (cons (car lst) head) target tail)))))

(defun get-arg ()
  (or
   #+CLISP ext:*args*
   #+SBCL sb-ext:*posix-argv*
   nil))

(defun flatten (lst)
  (loop :for (dep . val) :in lst :append (list dep val) :into res :finally (return res)))

                                        ; Parser
(defun parse-one (str pred)
  (if (null str)
      (values nil nil)
      (if (funcall pred (car str))
          (values (car str) (cdr str))
          (values nil str))))

(defun parse-any (str pred)
  (if (null str)
      (values nil nil)
      (slet ((res rest (parse-one str pred)))
        (if res
            (slet ((nxt nxtr (parse-any rest pred)))
              (values (cons res nxt) nxtr))
            (values res rest)))))

(defun parse-or (str &rest parsers)
  (if (or (null parsers)
          (null str))
      (values nil str)
      (slet ((res rest (funcall (car parsers) str)))
        (if res
            (values res rest)
            (apply #'parse-or (cons str (cdr parsers)))))))

(defun parse-space (str)
  (parse-any str (lm c (member c '(#\Space #\Tab #\Linefeed #\Return)))))

(defun parse-symbol (str)
  (slet ((sym rest (parse-any str #'alpha-char-p)))
    (if sym
        (values
         (chars->str sym)
         rest)
        (values nil str))))

(defun skip-space (str)
  (slet ((space rest (parse-space str)))
    (declare (ignore space))
    rest))

(defun parse-keyword (str kw)
  (slet ((sym rest (parse-symbol str)))
    (if (equalp sym kw)
        (values sym rest)
        (values nil str))))

(defun parse-neg (str)
  (parse-keyword str "neg"))

(defun parse-binop (str)
  (parse-or str
            (lm s (parse-keyword s "and"))
            (lm s (parse-keyword s "or"))
            (lm s (parse-keyword s "imp"))
            (lm s (parse-keyword s "iff"))))

(defun parse-neg-form (str)
  (slet ((neg rest (parse-neg str)))
    (if neg
        (slet ((form srest (parse-formula (skip-space rest))))
          (if form
              (values (list 'neg form) srest)
              (values nil str)))
        (values nil str))))

(defun kwp (sym)
  (member sym '("and" "or" "imp" "iff" "neg" "seq") :test #'equalp))

(defun %parse-bin-form (str lhs)
  (slet ((op rest (parse-binop str)))
    (if op
        (slet ((rhs rrest (parse-or (skip-space rest) #'parse-atomic #'parse-paren-form)))
          (if rhs
              (values (list (intern (string-upcase op)) lhs rhs) rrest)
              (values lhs str)))
        (values lhs str))))

(defun parse-bin-form (str)
  (slet ((lhs rest (parse-or str #'parse-atomic #'parse-paren-form)))
    (if lhs
        (%parse-bin-form (skip-space rest) lhs)
        (values nil str))))

(defun parse-atomic (str)
  (slet ((sym rest (parse-symbol str)))
    (if (and sym (not (kwp sym)))
        (if (let ((next (parse-symbol rest)))
              (if next
                  (kwp next)
                  nil))
            (values nil str)
            (values (intern sym) rest))
        (values nil str))))

(defun parse-paren-form (str)
  (slet ((lparen rest (parse-one str (lm c (equalp c #\( )))))
    (if lparen
        (slet ((inner rrest (parse-formula (skip-space rest))))
          (if inner
              (slet ((rparen rrrest (parse-one (skip-space rrest) (lm c (equalp c #\) )))))
                (if rparen
                    (values inner rrrest)
                    (values nil str)))))
        (values nil str))))


(defun parse-formula (str)
  (parse-or str #'parse-neg-form #'parse-bin-form))

(defun parse-list (str)
  (slet ((lbrk rest (parse-one str (lm c (equalp c #\[)))))
    (if lbrk
        (labels
            ((parse-inner (str)
               (slet ((formula rest (parse-formula str)))
                 (cond
                   ((equalp (car str) #\])
                    (values nil (skip-space (cdr str))))
                   ((equalp (car str) #\,)
                    (parse-inner (skip-space (cdr str))))
                   (formula
                    (slet ((next nextr (parse-inner (skip-space rest))))
                      (values (cons formula next) nextr)))
                   (t
                    (values nil str))))))
          (parse-inner (skip-space rest)))
        (values nil str))))

(defun parse-input (str)
  (let ((chars (str->chars str)))
    (slet ((lhs rest (parse-list chars)))
      (slet ((seq resto (parse-keyword (skip-space rest) "seq")))
        (when seq
          (slet ((rhs rest (parse-list (skip-space resto))))
            (when (null rest)
              (list 'seq lhs rhs))))))))

                                        ; Processing
(defun %atomic-form-p (form)
  (loop :for f :in form :always (symbolp f)))

(defun atomic-form-p (form)
  (when (equalp 'seq (car form))
    (and (%atomic-form-p (cadr form))
         (%atomic-form-p (caddr form)))))

                                        ; Rules (reversed)
(defun +p1+ (form)
  (when (equalp 'seq (car form))
    (and (atomic-form-p form)
         (intersection (cadr form) (caddr form)))))

(defun +p2a+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form))
          (rhs (caddr form)))
      (slet ((head neg tail (split-at rhs  (lm f (and (consp f) (equalp 'neg (car f)))))))
        (if (null neg)
            nil
            (list (list 'seq (cons (cadr neg) lhs) (concatenate 'list head tail))))))))

(defun +p2b+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head neg tail (split-at lhs (lm f (and (consp f) (equalp 'neg (car f)))))))
        (if (null neg)
            nil
            (list (list 'seq (concatenate 'list head tail) (append rhs (cdr neg)))))))))

(defun +p3a+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head andf tail (split-at rhs (lm f (and (consp f) (equalp 'and (car f)))))))
        (if (null andf)
            nil
            (list (list 'seq lhs (concatenate 'list head (list (cadr andf)) tail))
                  (list 'seq lhs (concatenate 'list head (list (caddr andf)) tail))))))))

(defun +p3b+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head andf tail (split-at lhs (lm f (and (consp f) (equalp 'and (car f)))))))
        (if (null andf)
            nil
            (list (list 'seq (concatenate 'list head (cdr andf) tail) rhs)))))))

(defun +p4a+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head orf tail (split-at rhs (lm f (and (consp f) (equalp 'or (car f)))))))
        (if (null orf)
            nil
            (list (list 'seq lhs (concatenate 'list head (cdr orf) tail))))))))

(defun +p4b+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head orf tail (split-at lhs (lm f (and (consp f) (equalp 'or (car f)))))))
        (if (null orf)
            nil
            (list (list 'seq (concatenate 'list head (list (cadr orf)) tail) rhs)
                  (list 'seq (concatenate 'list head (list (caddr orf)) tail) rhs)))))))

(defun +p5a+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head imp tail (split-at rhs (lm f (and (consp f) (equalp 'imp (car f)))))))
        (if (null imp)
            nil
            (list (list 'seq (append lhs (list (cadr imp))) (concatenate 'list head (list (caddr imp)) tail))))))))

(defun +p5b+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head imp tail (split-at lhs (lm f (and (consp f) (equalp 'imp (car f)))))))
        (if (null imp)
            nil
            (list (list 'seq (concatenate 'list head (list (caddr imp)) tail) rhs)
                  (list 'seq (concatenate 'list head tail) (append rhs (list (cadr imp))))))))))

(defun +p6a+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head iff tail (split-at rhs (lm f (and (consp f) (equalp 'iff (car f)))))))
        (if (null iff)
            nil
            (list (list 'seq
                        (cons (cadr iff) lhs)
                        (concatenate 'list head (list (caddr iff)) tail))
                  (list 'seq
                        (cons (caddr iff) lhs)
                        (concatenate 'list head (list (cadr iff)) tail))))))))

(defun +p6b+ (form)
  (when (equalp 'seq (car form))
    (let ((lhs (cadr form)) (rhs (caddr form)))
      (slet ((head iff tail (split-at lhs (lm f (and (consp f) (equalp 'iff (car f)))))))
        (if (null iff)
            nil
            (list (list 'seq
                        (concatenate 'list head (cdr iff) tail)
                        rhs)
                  (list 'seq
                        (concatenate 'list head tail)
                        (append rhs (cdr iff)))))))))

(defvar rules
  '((|P2a| +p2a+)
    (|P2b| +p2b+)
    (|P3a| +p3a+)
    (|P3b| +p3b+)
    (|P4a| +p4a+)
    (|P4b| +p4b+)
    (|P5a| +p5a+)
    (|P5b| +p5b+)
    (|P6a| +p6a+)
    (|P6b| +p6b+)))

                                        ; Searching
(defun %%search (form)
;  (format *standard-output* "%%Search form : ~A~%" form)
  (if (+p1+ form)
      '((p1))
      (when form
        (loop :for (name rule) :in rules
              :when (funcall rule form)
                :collect (list (funcall rule form) name)))))

(defun %search (forms)
;  (format *standard-output* "%search form : ~a~%" forms)
  (let ((next-steps
          (loop :for form :in forms
;                :do (format *standard-output* "form: ~A~%" (car form))
                :append (mapcar #'(lambda (f)
                                     (-> f
                                       #'%%search
                                       (lm ns (mapcar (lm n (append n form)) ns))))
                                 (car form))
                  :into res
                :finally (return res))))
;    (format *standard-output* "Next-Steps: ~A~%" next-steps)
    (or (car (member-if (lm head (equalp 'p1 head)) next-steps :key #'caar))
        (loop :for step :in next-steps
              :append (%search step)
                :into res
              :finally (return res)))))

(defun search-resol (form)
;  (format *standard-output* "Search form: ~A~%" form)
  (if (+p1+ form)
      'trivial-p1
      (%search
       (loop :for (name rule) :in rules
             :when (funcall rule form)
               :collect (list (funcall rule form) name (list form))))))

                                        ; Interaction
(defun pretty-print-form (form)
  (if (consp form)
      (case (car form)
        (seq
         (let ((lhs (cadr form))
               (rhs (caddr form)))
           (format nil "[~{~a~^, ~}] seq [~{~a~^, ~}]" (mapcar #'pretty-print-form lhs) (mapcar #'pretty-print-form rhs))))
        ((imp iff and or)
         (let ((lhs (cadr form))
               (rhs (caddr form)))
           (if (or (consp lhs) (consp rhs))
               (format nil "(~a ~a ~a)" (pretty-print-form lhs) (string-downcase (symbol-name (car form))) (pretty-print-form rhs))
               (format nil "~a ~a ~a" lhs (string-downcase (symbol-name (car form))) rhs))))
        (neg
         (let ((exp (cadr form)))
           (if (consp exp)
               (format nil "neg (~A)" (pretty-print-form exp))
               (format nil "neg ~A" exp)))))
      (format nil "~A" form)))

(defun print-res (res)
  (labels ((fold (lst)
             (when lst
               (cons (list (car lst) (cadr lst)) (fold (cddr lst))))))
    (let* ((res (mapcar (lm r (list (car r) (mapcar #'pretty-print-form (cadr r)))) (fold res)))
           (max-len (apply #'max (mapcar #'length (flatten (concatenate 'list (mapcar #'cadr res)))))))
      (loop :for (rule form) :in res :do (format *standard-output* "~{~A~^~%~} ~{~A~} Rule ~A~%" form (make-list (- max-len (length (car (last form)))) :initial-element " ") rule)))))

(defun solve (str)
  (let ((res (search-resol (parse-input str))))
    (if res
        (progn
          (format *standard-output* "true~%")
          (print-res (car res)))
      (format *standard-output* "false~%"))))

                                        ; Entrance
(solve (car (last (get-arg))))
