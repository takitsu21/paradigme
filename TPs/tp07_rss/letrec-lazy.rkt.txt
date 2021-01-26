; Cours 07 : letrec paresseux avec effets de bord
; !!!!! NE FONCTIONNE PAS !!!!!

#lang plait #:lazy

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [letrecE (s : Symbol) (rhs : Exp) (body : Exp)]
  [ifE (test-expr : Exp) (then-expr : Exp) (else-expr : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [undefV])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : (Boxof Value))])

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
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (multE (numE -1) (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (appE (lamE (s-exp->symbol (first subst)) (parse (third sl))) (parse (second subst)))))]
    [(s-exp-match? `{letrec {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letrecE (s-exp->symbol (first subst)) (parse (second subst)) (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (second sl))])
         (lamE (s-exp->symbol (first sll)) (parse (third sl)))))]
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
    [(letrecE s rhs body)
     (let ([b (box (undefV))])
       (let ([new-env (extend-env (bind s b) env)])
         (begin
           (set-box! b (interp rhs new-env))
           (interp body new-env))))]
    [(ifE cnd l r)
     (type-case Value (interp cnd env)
       [(numV n) (if (not (= n 0)) (interp l env) (interp r env))]
       [else (error 'interp "not a number")])]
    [(lamE par body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (box (interp arg env))) c-env))]
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
    [(equal? n (bind-name (first env))) (unbox (bind-val (first env)))]
    [else (lookup n (rest env))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))

;(interp-expr `{letrec {[x 1]} {+ x 2}})

;(interp-expr `{letrec {[f {lambda {x} {f x}}]} {f 1}})

;(interp-expr `{letrec {[f {lambda {x} {f x}}]} f})
