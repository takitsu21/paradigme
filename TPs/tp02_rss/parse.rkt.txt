; Cours 02 : Langage des expressions arithmétiques

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions dans le langage utilisateur
(define-type Exp
  [numE (n : Number)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp]) : Number
  (type-case Exp e
    [(numE n) n]
    [(plusE l r) (+ (interp l) (interp r))]
    [(multE l r) (* (interp l) (interp r))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [s : S-Exp]) : Number
  (interp (parse s)))

(test (interp-expr `1) 1)
(test (interp-expr `{+ 1 2}) 3)
(test (interp-expr `{* 2 3}) 6)
(test (interp-expr `{+ 1 {* 2 3}}) 7)