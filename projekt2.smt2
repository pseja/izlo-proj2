(set-logic NIA)

(set-option :produce-models true)
(set-option :incremental true)

; Deklarace promennych pro vstupy
; ===============================

; Parametry
(declare-fun A () Int)
(declare-fun B () Int)
(declare-fun C () Int)
(declare-fun D () Int)
(declare-fun E () Int)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;; START OF SOLUTION ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; if ((D <= 0) or (E <= 0)) {return false;}
(assert (and (> D 0) (> E 0)))

; int x, y, z;
(declare-fun x () Int) (declare-fun y () Int) (declare-fun z () Int)

; x = A * B * 2;
(assert (= x (* A B 2)))

; x < E
(assert (ite (< x E)
                (= y (+ x (* 5 B))) ; x < E == true  -> y = 5*B + x
                (= y (- x C))))     ; x < E == false -> y = x - C

; (y + 2) < D
(assert (ite (< (+ y 2) D) 
                (= z (- (* x A) (* y B)))   ; y+2 < D == true  -> z = x*A - y*B
                (= z (+ (* x B) (* y A))))) ; y+2 < D == false -> z = x*B + y*A

; z >= (E + D) == false
(assert (< z (+ E D)))

; E + D lowest possible
(assert
  (forall ((D1 Int) (E1 Int) (x1 Int) (y1 Int) (z1 Int))
    (=>
        (and
            (> D1 0)
            (> E1 0)
            (= x1 (* A B 2))
            (ite (< x1 E1) 
                    (= y1 (+ x1 (* 5 B)))
                    (= y1 (- x1 C))
            )
            (ite (< (+ y1 2) D1)
                    (= z1 (- (* x1 A) (* y1 B)))
                   (= z1 (+ (* x1 B) (* y1 A)))
           )
            (< z1 (+ E1 D1))
        ) (<= (+ D E) (+ D1 E1))
   )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; END OF SOLUTION ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Testovaci vstupy
; ================

(echo "Test 1 - vstup A=1, B=1, C=3")
(echo "a) Ocekavany vystup je sat a D+E se rovna 2")
(check-sat-assuming (
  (= A 1) (= B 1) (= C 3)
))
(get-value (D E (+ D E)))
(echo "b) Neexistuje jine reseni nez 2, ocekavany vystup je unsat")
(check-sat-assuming (
  (= A 1) (= B 1) (= C 3) (distinct (+ D E) 2)
))


(echo "Test 2 - vstup A=5, B=2, C=5")
(echo "a) Ocekavany vystup je sat a D+E se rovna 54")
(check-sat-assuming (
  (= A 5) (= B 2) (= C 5)
))
(get-value (D E (+ D E)))
(echo "b) Neexistuje jine reseni nez 54, ocekavany vystup je unsat")
(check-sat-assuming (
  (= A 5) (= B 2) (= C 5) (distinct (+ D E) 54)
))

(echo "Test 3 - vstup A=100, B=15, C=1")
(echo "a) Ocekavany vystup je sat a D+E se rovna 253876")
(check-sat-assuming (
  (= A 100) (= B 15) (= C 1)
))
(get-value (D E (+ D E)))
(echo "b) Neexistuje jine reseni nez 253876, ocekavany vystup je unsat")
(check-sat-assuming (
  (= A 100) (= B 15) (= C 1) (distinct (+ D E) 253876)
))

(echo "Test 4 - vstup A=5, B=5, C=3")
(echo "a) Ocekavany vystup je sat a D+E se rovna 51")
(check-sat-assuming (
  (= A 5) (= B 5) (= C 3)
))
(get-value (D E (+ D E)))
(echo "b) Neexistuje jine reseni nez 51, ocekavany vystup je unsat")
(check-sat-assuming (
  (= A 5) (= B 5) (= C 3) (distinct (+ D E) 51)
))

(echo "Test 5 - vstup A=2, B=1, C=2")
(echo "a) Ocekavany vystup je sat a D+E se rovna 7")
(check-sat-assuming (
  (= A 2) (= B 1) (= C 2)
))
(get-value (D E (+ D E)))
(echo "b) Neexistuje jine reseni nez 7, ocekavany vystup je unsat")
(check-sat-assuming (
  (= A 2) (= B 1) (= C 2) (distinct (+ D E) 7)
))
