; Cours 08 : Continuations

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [appE (fun : Exp) (arg : Exp)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des continuations
(define-type Cont
  [doneK]
  [addSecondK (r : Exp) (env : Env) (k : Cont)]
  [doAddK (val : Value) (k : Cont)]
  [multSecondK (r : Exp) (env : Env) (k : Cont)]
  [doMultK (val : Value) (k : Cont)]
  [appArgK (arg : Exp) (env : Env) (k : Cont)]
  [doAppK (val : Value) (k : Cont)])

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
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (multE (numE -1) (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (appE (lamE (s-exp->symbol (first subst)) (parse (third sl))) (parse (second subst)))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [k : Cont]) : Value
  (type-case Exp e
    [(numE n) (continue k (numV n))]
    [(idE s) (continue k (lookup s env))]
    [(plusE l r) (interp l env (addSecondK r env k))]
    [(multE l r) (interp l env (multSecondK r env k))]
    [(lamE par body) (continue k (closV par body env))]
    [(appE f arg) (interp f env (appArgK arg env k))]))

; Appel des continuations
(define (continue [k : Cont] [val : Value]) : Value
  (type-case Cont k
    [(doneK) val]
    [(addSecondK r env next-k) (interp r env (doAddK val next-k))]
    [(doAddK v-l next-k) (continue next-k (num+ v-l val))]
    [(multSecondK r env next-k) (interp r env (doMultK val next-k))]
    [(doMultK v-l next-k) (continue next-k (num* v-l val))]
    [(appArgK arg env next-k) (interp arg env (doAppK val next-k))]
    [(doAppK v-f next-k)
     (type-case Value v-f
       [(closV par body c-env)
        (interp body (extend-env (bind par val) c-env) next-k)]
       [else (error 'interp "not a function")])]))

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
(define (lookup [n : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))]
    [else (lookup n (rest env))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env (doneK)))
