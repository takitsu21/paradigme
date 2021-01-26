; Cours 03 : Environnement

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
  [appE (fun : Symbol) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)])

; Représentation des définitions de fonctions
(define-type FunDef
  [fd (name : Symbol) (par : Symbol) (body : Exp)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Number)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

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
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
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
(define (interp [e : Exp] [env : Env] [fds : (Listof FunDef)]) : Number
  (type-case Exp e
    [(numE n) n]
    [(idE s) (lookup s env)]
    [(plusE l r) (+ (interp l env fds) (interp r env fds))]
    [(multE l r) (* (interp l env fds) (interp r env fds))]
    [(appE f arg)
     (let [(fd (get-fundef f fds))]
       (interp (fd-body fd)
               (extend-env (bind (fd-par fd) (interp arg env fds)) mt-env)
               fds))]
    [(letE s rhs body)
     (interp body
             (extend-env (bind s (interp rhs env fds)) env)
             fds)]))

; Recherche d'une fonction parmi les définitions
(define (get-fundef [s : Symbol] [fds : (Listof FunDef)]) : FunDef
  (cond
    [(empty? fds) (error 'get-fundef "undefined function")]
    [(equal? s (fd-name (first fds))) (first fds)]
    [else (get-fundef s (rest fds))]))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Number
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))]
    [else (lookup n (rest env))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp] [fds : (Listof S-Exp)]) : Number
  (interp (parse e) mt-env (map parse-fundef fds)))

(test (interp-expr `{double 3}
                   (list `{define {double x} {+ x x}}))
      6)

(test (interp-expr `{quadruple 3}
                   (list `{define {double x} {+ x x}}
                         `{define {quadruple x} {double {double x}}}))
      12)
