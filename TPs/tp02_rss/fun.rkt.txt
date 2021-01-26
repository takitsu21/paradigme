; Cours 02 : Fonctions

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [appE (fun : Symbol) (arg : Exp)])

; Représentation des définitions de fonctions
(define-type FunDef
  [fd (name : Symbol) (par : Symbol) (body : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (s-exp->symbol (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-fundef [s : S-Exp]) : FunDef
  (if (s-exp-match? `{define {SYMBOL SYMBOL} ANY} s)
      (let ([sl (s-exp->list s)])
        (let ([sl2 (s-exp->list (second sl))])
          (fd (s-exp->symbol (first sl2)) 
              (s-exp->symbol (second sl2))
              (parse (third sl)))))
      (error 'parse-fundef "invalid input")))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [fds : (Listof FunDef)]) : Number
  (type-case Exp e
    [(numE n) n]
    [(idE s) (error 'interp "free identifier")]
    [(plusE l r) (+ (interp l fds) (interp r fds))]
    [(multE l r) (* (interp l fds) (interp r fds))]
    [(appE f arg) (let [(fd (get-fundef f fds))]
                    (interp (subst (numE (interp arg fds))
                                   (fd-par fd)
                                   (fd-body fd))
                            fds))]))

; Recherche d'une fonction parmi les définitions
(define (get-fundef [s : Symbol] [fds : (Listof FunDef)]) : FunDef
  (cond
    [(empty? fds) (error 'get-fundef "undefined function")]
    [(equal? s (fd-name (first fds))) (first fds)]
    [else (get-fundef s (rest fds))]))

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in
    [(numE n) in]
    [(idE s) (if (equal? for s) what in)]
    [(plusE l r) (plusE (subst what for l) (subst what for r))]
    [(multE l r) (multE (subst what for l) (subst what for r))]
    [(appE f arg) (appE f (subst what for arg))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp] [fds : (Listof S-Exp)]) : Number
  (interp (parse e) (map parse-fundef fds)))

(test (interp-expr `{double 3}
                   (list `{define {double x} {+ x x}}))
      6)

(test (interp-expr `{quadruple 3}
                   (list `{define {double x} {+ x x}}
                         `{define {quadruple x} {double {double x}}}))
      12)
