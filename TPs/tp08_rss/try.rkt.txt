; Cours 08 : Instruction try

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
  [lamE (par : Symbol) (body : Exp)]
  [tryE (body : Exp) (handler : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [errorV (msg : String)])

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
  [doAppK (val : Value) (k : Cont)]
  [tryK (handler : Exp) (env : Env) (k : Cont)])

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
    [(s-exp-match? `{try ANY {lambda {} ANY}} s)
     (let ([sl (s-exp->list s)])
       (tryE (parse (second sl)) (parse (third (s-exp->list (third sl))))))]
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
    [(idE s) (lookup s env k)]
    [(plusE l r) (interp l env (addSecondK r env k))]
    [(multE l r) (interp l env (multSecondK r env k))]
    [(lamE par body) (continue k (closV par body env))]
    [(appE f arg) (interp f env (appArgK arg env k))]
    [(tryE body handler) (interp body env (tryK handler env k))]))

; Appel des continuations
(define (continue [k : Cont] [val : Value]) : Value
  (type-case Cont k
    [(doneK) val]
    [(addSecondK r env next-k) (interp r env (doAddK val next-k))]
    [(doAddK v-l next-k) (num+ v-l val next-k)]
    [(multSecondK r env next-k) (interp r env (doMultK val next-k))]
    [(doMultK v-l next-k) (num* v-l val next-k)]
    [(appArgK arg env next-k) (interp arg env (doAppK val next-k))]
    [(doAppK v-f next-k)
     (type-case Value v-f
       [(closV par body c-env)
        (interp body (extend-env (bind par val) c-env) next-k)]  
       [else (escape k (errorV "not a function"))])]
    [(tryK handler env next-k) (continue next-k val)]))

; Lancement des exceptions
(define (escape [k : Cont] [val : Value]) : Value
  (type-case Cont k
    [(doneK) val]
    [(addSecondK r env next-k) (escape next-k val)]
    [(doAddK v-l next-k) (escape next-k val)]
    [(multSecondK r env next-k) (escape next-k val)]
    [(doMultK v-l next-k) (escape next-k val)]
    [(appArgK arg env next-k) (escape next-k val)]
    [(doAppK v-f next-k) (escape next-k val)]
    [(tryK handler env next-k) (interp handler env next-k)]))

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value] [k : Cont]): Value
  (if (and (numV? l) (numV? r))
      (continue k (numV (op (numV-n l) (numV-n r))))
      (escape k (errorV "not a number"))))

(define (num+ [l : Value] [r : Value] [k : Cont]) : Value
  (num-op + l r k))

(define (num* [l : Value] [r : Value] [k : Cont]) : Value
  (num-op * l r k))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env] [k : Cont]) : Value
  (cond
    [(empty? env) (escape k (errorV "free identifier"))]
    [(equal? n (bind-name (first env))) (continue k (bind-val (first env)))]
    [else (lookup n (rest env) k)]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env (doneK)))