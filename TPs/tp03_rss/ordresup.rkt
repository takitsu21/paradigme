; Cours 03 : Ordre supérieur

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
  [ifE (first : Exp) (second : Exp) (third : Exp)]
  [boolE (b : Boolean)]
  [equalE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [boolV (b : Boolean)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

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

(define (testz [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (if (equal? s `true)
                                  (boolE #t)
                                  (idE (s-exp->symbol s)))]
    [else (boolE #f)]))

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (if (equal? s `true)
                                  (boolE #t)
                                  (idE (s-exp->symbol s)))]
    [(s-exp-match? `{= ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (equalE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(boolE b) (boolV b)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(lamE par body) (closV par body env)]
    [(equalE l r) (num= (interp l env) (interp r env))]
    [(ifE first second third) (num-if first second third env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(letE s rhs body) (interp body (extend-env (bind s (interp rhs env)) env))]))

(define (num-if [first : Exp]
                [second : Exp]
                [third : Exp]
                [env : Env]) : Value
  (if (not (boolV? (interp first env)))
      (error 'interp "not a boolean")
      (if (boolV? (interp first env))
          (interp second env)
          (interp third env))))

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num-op-equal [op : (Number Number -> Boolean)]
                      [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (boolV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))


(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num= [l : Value] [r : Value]) : Value
  (num-op-equal = l r))

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
(define (true) #t)
(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))

(test (interp-expr `{let {[f {lambda {x} {+ 1 x}}]} {f 2}})
      (numV 3))

(test (interp-expr `{let {[y 1]} {lambda {x} {+ x y}}})
      (closV 'x (plusE (idE 'x) (idE 'y)) (extend-env (bind 'y (numV 1)) mt-env)))

(test (interp-expr `{let {[y 1]} {{lambda {x} {+ x y}} 2}})
      (numV 3))

(test (interp-expr `{= 1 2}) (boolV #f))
(test/exn (interp-expr `{= true true}) "not a number")
(test (interp-expr `{if true 1 2}) (numV 1))
(test (interp-expr `{if {= {+ 1 3} {* 2 2}} 4 5}) (numV 4))
(test/exn (interp-expr `{if 1 2 3}) "not a boolean")
(test (interp-expr `{if true 1 x}) (numV 1))