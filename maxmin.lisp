;; Maxima functions for finding the maximum or minimum
;; Copyright (C) 2005, 2007, 2021 Barton Willis

;; Barton Willis
;; Department of Mathematics, 
;; University of Nebraska at Kearney
;; Kearney NE 68847
;; willisb@unk.edu

;; This source code is licensed under the terms of the Lisp Lesser 
;; GNU Public License (LLGPL). The LLGPL consists of a preamble, published
;; by Franz Inc. (http://opensource.franz.com/preamble.html), and the GNU 
;; Library General Public License (LGPL), version 2, or (at your option)
;; any later version.  When the preamble conflicts with the LGPL, 
;; the preamble takes precedence. 

;; This library is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; Library General Public License for details.

;; You should have received a copy of the GNU Library General Public
;; License along with this library; if not, write to the
;; Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
;; Boston, MA  02110-1301, USA.

(in-package :maxima)
(macsyma-module maxmin)

(eval-when (:compile-toplevel :load-toplevel :execute)
  ($put '$maxmin 2 '$version)   ;; Let's have version numbers 1,2,3,...
  ;; Let's remove built-in symbols from list for user-defined properties.
  (setq $props (remove '$maxmin $props)))

(defprop $max $max verb)
(defprop $min $min verb)

(defmvar $maxmin_effort 10)
(defun maxmin_effort-assign (xx y)
  (declare (ignore xx))
  (cond ((and (integerp y) (> y -1))
          (setq $maxmin_effort y))
        (t 
          (merror (intl:gettext "The value of maxmin_effort must be a nonnegative integer; found ~M ~%") y))))

(defprop $maxmin_effort maxmin_effort-assign assign)
;; Return true if there is pi in the CL list p and qi in the CL lisp q such that
;; x is between pi and qi.  This means that either pi <= x <= qi or
;; qi <= x <= pi. For example, 2x is between x and 3x.

;; Strangely, sign((a-b)*(b-a)) --> pnz but sign(expand((a-b)*(b-a))) --> nz.
;; To workaround this weirdness, we could call expand instead of factor on 
;; (mul (sub x pk) (sub qk x))), but let's not do that.

;; The betweenp simplification is done last; this has some interesting effects:
;; max(x^2,x^4,x^6,x^2+1) (standard simplification) --> max(x^4,x^6,x^2+1) 
;; (betweenp) --> max(x^4,x^6,x^2+1). If the betweenp simplification were done 
;; first, we'd have max(x^2,x^4,x^6,x^2+1) --> max(x^2,x^6,x^2+1) --> max(x^6,x^2+1).

;; The function $factor refuses to factor an expression that has an exponent that
;; exceeds factor_max_degree. I think this is a better heuristic than the conssize
;; method used by factor-if-small (defined in compar.lisp). So let's use $factor, not
;; factor-if-small. We could locally set the value of factor_max_degree, but let's not.

;; Removing factor from (csign ($factor (mul (sub x pk) (sub qk x))) causes max
;; to miss the simplification max(x^2,x^4,x^6) --> max(x^2, x^4). Arguably, csign
;; should be more semantically neutral--until it is, let's keep factor in here.
(defun betweenp (x p q)
  (catch 'done
      (dolist (pk p)
	      (dolist (qk q)
            (when (member (csign ($factor (mul (sub x pk) (sub qk x))))
                   '($pos $pz) :test #'eq) 
              (throw 'done t))))))

;; Return true if y is the additive inverse of x. 
(defun add-inversep (x y)
  (eq t (meqp x (neg y))))

;; Define a simplim%function to handle a limit of $max.
(defprop $max simplim$max simplim%function)

(defun simplim$max (expr var val)
  (simplifya (cons '($max) (mapcar #'(lambda (e) (limit e var val 'think)) (cdr expr))) t))

(defprop $max simp-max operators)

;; True iff e is a GRE expression of the form max(...)
(defun max-p (e)
  (and (consp e) (eq (caar e) '$max)))

; True iff e is a GRE expression of the form min(...)
(defun min-p (e)
  (and (consp e) (eq (caar e) '$min)))

;; Undone:  max(1-x,1+x) - max(x,-x) --> 1.

(defun simp-max (l tmp z)
  (declare (ignore tmp))
  (let ((acc nil) (sgn) (num-max nil) (issue-warning))
    (setq l (cdr  l))

    ;; When maxmin_effort > 0, simplify each member of l and flatten (that is, do
    ;; max(a,max(a,b)) -> max(a,b,c)). The effort for this step is O(n).
    (when (> $maxmin_effort 0)
      (dolist (li l)
          (setq li (simplifya (specrepcheck li) z))
          (cond 
            ((max-p li)
              (setq acc (append acc (cdr li))))
            ((and (not (eq li '$minf)) (not (alike1 '((mtimes) -1 $inf) li)))
              (push li acc))))
      (setq l acc))

    ;(mtell "at 1:  l = ~M ~%" (cons '(mlist) l))
    ;; Find the largest real number in l. Since (mnump '$%i) --> false, we don't 
    ;; have to worry that num-max is complex. The effort for this step is O(n).  
    (when (> $maxmin_effort 0)
      (setq acc nil)         
      (dolist (li l)
         (if (mnump li) 
         (setq num-max (if (or (null num-max) (mgrp li num-max)) li num-max)) (push li acc)))
      
      (when num-max
        (push num-max acc))
      (setq l acc))

    ;(mtell "at 2:  l = ~M ~%" (cons '(mlist) l))
    ;; Sort and remove duplicates.  The effort for this step is O(n logn)).  
    (when (> $maxmin_effort 0)  
      (setq l (sorted-remove-duplicates (sort l '$orderlessp))))

     ;(mtell "at 3:  l = ~M ~%" (cons '(mlist) l))
    ;; When maxmin_effort > 2, if e and -e are members of l, replace e & -e by
    ;; abs(e).     
    (when (> $maxmin_effort 2)
        (let ((pp) (qq) (nn))
          (setq pp (simplifya (cons '($set) l) t))
          (setq qq (simplifya (cons '($set) (mapcar #'limitneg l)) t))
          (setq nn ($intersection pp qq))
          (setq pp ($setdifference pp nn))
          (when (not ($emptyp nn))
              (setq nn (mapcar #'(lambda (s) (take '(mabs) s)) (cdr nn)))
              (setq nn (simplifya (cons '($set) nn) t))
              (setq pp ($union pp nn)))
          (setq l (cdr pp))))
    
    ;; Accumulate the maximum in the list acc. For each x in l, do:
    ;; (a) if x is > or >= every member of acc, set acc to (x),
    ;; (b) if x is < or <= to some member of acc, do nothing,
    ;; (c) if neither 'a' or 'b', push x into acc,
    ;; (d) if x cannot be compared to some member of acc, set issue-warning to true.
    (when (> $maxmin_effort 1)
      (setq acc nil)
      (dolist (x l)
        (catch 'done
          (dolist (ai acc)
	            (setq sgn ($compare x ai))
	            (cond ((member sgn '(">" ">=") :test #'equal)
		                    (setq acc (delete ai acc :test #'eq)))
	                  ((eq sgn '$notcomparable) (setq issue-warning t))
	                  ((member sgn '("<" "=" "<=") :test #'equal)
		                  (throw 'done t))))
               (push x acc)))
      (setq l acc))
  
    ;(mtell "at 5:  l = ~M ~%" (cons '(mlist) l))
    ;; When issue-warning is false and maxmin_effort > 2, use the betweenp 
    ;; simplification.
    (when (and (not issue-warning) (> $maxmin_effort 2))
	    (setq acc nil)
	    (setq sgn (cdr l))
	    (dolist (ai l)
	      (when (not (betweenp ai sgn sgn)) 
           (push ai acc))
	      (setq sgn `(,@(cdr sgn) ,ai)))
	    (setq l acc))

    ;(mtell "at 6:  l = ~M ~%" (cons '(mlist) l))  
    ;; Finally, do a few clean ups:    
    (setq l (if (not issue-warning) (delete '$minf l) l))
    (cond ((null l) '$minf) ;max(emptyset) -> minf.
          ((and (not issue-warning) (member '$inf l :test #'eq)) '$inf)
          ((null (cdr l)) (car l)) ;singleton case: max(xx) --> xx
          (t  `(($max simp) ,@(sort l '$orderlessp)))))) ;nounform return.

;; Return -x, but check for the special cases x = inf, minf, und, ind, and infinity.
;; Also locally set negdistrib to true (this is what the function neg does). We could
;; do -zeroa -> zerob and -zerob -> zeroa, I suppose. 

;; To catch more cases, replace this function body with ($limit (mul -1 x)).
;; But ($limit (mul -1 x)) misses the case -ind --> ind & limit can be costly. 
(defun limitneg (x)
  (cond ((eq x '$minf) '$inf) ; -minf -> inf
      	((eq x '$inf) '$minf) ; -inf -> minf
	      ((member x '($und $ind $infinity) :test #'eq) x) ;-und -> und, and ...
      	(t (let (($negdistrib t)) (mul -1 x))))) ; x -> -x

;; Define a simplim%function to handle a limit of $min.

(defprop $min simplim$min simplim%function)

(defun simplim$min (expr var val)
 (simplifya (cons '($min) (mapcar #'(lambda (e) (limit e var val 'think)) 
    (cdr expr))) t))

(defprop $min simp-min operators)

;; The function simp-min mostly piggy-backs onto simp-max. That is, we use
;; min(a,b,...) = -max(-a,-b,...).
(defun simp-min (l tmp z)
  (declare (ignore tmp))
  (let ((acc nil))
    (setq l (cdr l))
    (dolist (li l)
      (setq li (simplifya (specrepcheck li) z)) 
      ;; convert min(a, min(b,c)) --> min(a,b,c)
      (cond ((min-p li)
              (setq acc (append acc (cdr li))))
            (t
              (push li acc))))
    (setq l (mapcar #'limitneg acc))
    (setq l (simplifya (cons '($max) l) t))
    ;; Is the sort needed? I think so, but need a test that requires sorting...
    (if (max-p l)
      (cons (list '$min 'simp) (sort (mapcar  #'limitneg (cdr l)) '$orderlessp)) 
        (limitneg l))))

;; Several functions (derivdegree for example) use the maximin function. Here is 
;; a replacement that uses simp-min or simp-max.

(defun maximin (l op) (simplify `((,op) ,@l)))
 
(defmfun $lmax (e)
  (simplify `(($max) ,@(require-list-or-set e '$lmax)))) 

(defmfun $lmin (e)
  (simplify `(($min) ,@(require-list-or-set e '$lmin))))

;; Return the narrowest comparison operator op (<, <=, =, >, >=) such that
;; a op b evaluates to true. Return 'unknown' when either there is no such 
;; operator or when  Maxima's sign function isn't powerful enough to determine
;; such an operator; when Maxima is able to show that either argument is not 
;; real valued, return 'notcomparable.'

;; The subtraction can be a problem--for example, compare(0.1, 1/10)
;; evaluates to "=". But for flonum floats, I believe 0.1 > 1/10. 
;; If you want to convert flonum and big floats to exact rational
;; numbers, use $rationalize.

;; I think compare(asin(x), asin(x) + 1) should evaluate to < without
;; being quizzed about the sign of x. Thus the call to lenient-extended-realp.

(defmfun $compare (a b)
  ;(mtell "compare ~M ~M ~%" a b)
  ;; Simplify expressions with infinities, indeterminates, or infinitesimals.
  ;; Without these checks, we can get odd questions such as "Is 1 zero or nonzero?"
  (when (amongl '($ind $und $inf $minf $infinity $zeroa $zerob) a)
    (setq a ($limit a)))
  (when (amongl '($ind $und $inf $minf $infinity $zeroa $zerob) b)
    (setq b ($limit b)))
  
  (cond 
    ((or (amongl '($infinity $ind $und) a)
         (amongl '($infinity $ind $und) b)
         (not (lenient-extended-realp a))
         (not (lenient-extended-realp b)))
         (if (eq t (meqp a b)) "=" '$notcomparable))    
         
 	      (t (let ((sgn (csign (specrepcheck (sub a b)))))
	          (cond 
		          ((eq sgn '$neg) "<")
		          ((eq sgn '$nz) "<=")
		          ((eq sgn '$pz) ">=")
		          ((eq sgn '$pos) ">")
		          ((eq sgn '$pn) "#")
              ((eq sgn '$zero) "=")
		          (t '$unknown))))))

;; When it's fairly likely that the real domain of e is nonempty, return true; 
;; otherwise, return false. Even if z has been declared complex, the real domain
;; of z is nonempty; thus (lenient-extended-realp z) --> true.  When does this
;; function lie?  One example is acos(abs(x) + 2). The real domain of this 
;; expression is empty, yet lenient-extended-realp returns true for this input.

(defun lenient-extended-realp (e)
  (and ($freeof '$infinity '$%i '$und '$ind '$false '$true t nil e) ;; what else?
       (not (mbagp e))
       (not ($featurep e '$nonscalar))
       (not (mrelationp e))
       (not ($member e $arrays))))

(defun lenient-realp (e)
  (and ($freeof '$inf '$minf e) (lenient-extended-realp e)))

;; Convert all floats and big floats in e to an exact rational representation. 

(defmfun $rationalize (e)
  (setq e (ratdisrep e))
  (cond ((floatp e) 
	 (let ((significand) (expon) (sign))
	   (multiple-value-setq (significand expon sign) (integer-decode-float e))
	   (cl-rat-to-maxima (* sign significand (expt 2 expon)))))
	(($bfloatp e) (cl-rat-to-maxima (* (cadr e)(expt 2 (- (caddr e) (third (car e)))))))
	(($mapatom e) e)
	(t (simplify (cons (list (mop e)) (mapcar #'$rationalize (margs e)))))))
