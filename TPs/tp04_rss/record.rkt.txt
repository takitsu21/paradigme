; Cours 04 : Les enregistrements

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
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [recordE (fields : (Listof Symbol)) (args : (Listof Exp))]
  [getE (record : Exp) (field : Symbol)]
  [setE (record : Exp) (field : Symbol) (arg : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [recV (fields : (Listof Symbol)) (vals : (Listof Value))])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

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
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [(s-exp-match? `{record [SYMBOL ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (recordE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) (rest sl))
                (map (lambda (l) (parse (second (s-exp->list l)))) (rest sl))))]
    [(s-exp-match? `{get ANY SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (getE (parse (second sl)) (s-exp->symbol (third sl))))]
    [(s-exp-match? `{set ANY SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (parse (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(lamE par body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(letE s rhs body) (interp body (extend-env (bind s (interp rhs env)) env))]
    [(recordE fds args)
     (recV fds (map (lambda (expr) (interp expr env)) args))]
    [(getE rec fd)
     (type-case Value (interp rec env)
       [(recV fds vs) (find fd fds vs)]
       [else (error 'interp "not a record")])]
    [(setE rec fd arg)
     (type-case Value (interp rec env)
       [(recV fds vs) (recV fds (update fd (interp arg env) fds vs))]
       [else (error 'interp "not a record")])]))

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
    [else (lookup s (rest env))]))

; Recherche un symbole dans une liste de symboles et renvoie la valeur associée
(define (find [fd : Symbol] [fds : (Listof Symbol)] [vs : (Listof Value)]) : Value
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (first vs)]
    [else (find fd (rest fds) (rest vs))]))

; Recherche un symbole dans une liste de symboles
; Renvoie la liste initiale des valeurs avec modification
; de la valeur associée au symbole fd par new-val
(define (update [fd : Symbol] [new-val : Value]
                [fds : (Listof Symbol)] [vs : (Listof Value)]) : (Listof Value)
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (cons new-val (rest vs))]
    [else (cons (first vs) (update fd new-val (rest fds) (rest vs)))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))
