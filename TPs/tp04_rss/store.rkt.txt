; Cours 04 : Les boîtes avec mémoire explicite

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
  [boxE (val : Exp)]
  [unboxE (b : Exp)]
  [setboxE (b : Exp) (val : Exp)]
  [beginE (l : Exp) (r : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [boxV (l : Location)])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

; Manipulation de la mémoire
(define-type-alias Store (Listof Storage))
(define mt-store empty)
(define override-store cons)

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
    [(s-exp-match? `{box ANY} s)
     (let ([sl (s-exp->list s)])
       (boxE (parse (second sl))))]
    [(s-exp-match? `{unbox ANY} s)
     (let ([sl (s-exp->list s)])
       (unboxE (parse (second sl))))]
    [(s-exp-match? `{set-box! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (setboxE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store]) : Result
  (type-case Exp e
    [(numE n) (v*s (numV n) sto)]
    [(idE s) (v*s (lookup s env) sto)]
    [(plusE l r)
     (type-case Result (interp l env sto)
       [(v*s v-l sto-l)
        (type-case Result (interp r env sto-l)
          [(v*s v-r sto-r) (v*s (num+ v-l v-r) sto-r)])])]
    [(multE l r)
     (type-case Result (interp l env sto)
       [(v*s v-l sto-l)
        (type-case Result (interp r env sto-l)
          [(v*s v-r sto-r) (v*s (num* v-l v-r) sto-r)])])]
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (type-case Result (interp f env sto)
       [(v*s v-f sto-f)
        (type-case Value v-f
          [(closV par body c-env)
           (type-case Result (interp arg env sto-f)
             [(v*s v-arg sto-arg)
              (interp body (extend-env (bind par v-arg) c-env) sto-arg)])]
          [else (error 'interp "not a function")])])]
    [(letE s rhs body)
     (type-case Result (interp rhs env sto)
       [(v*s v-rhs sto-rhs)
        (interp body (extend-env (bind s v-rhs) env) sto-rhs)])]
    [(boxE val)
     (type-case Result (interp val env sto)
       [(v*s v-val sto-val)
        (let ([l (new-loc sto-val)])
          (v*s (boxV l) (override-store (cell l v-val) sto-val)))])]
    [(unboxE b)
     (type-case Result (interp b env sto)
       [(v*s v-b sto-b)
        (type-case Value v-b
          [(boxV l) (v*s (fetch l sto-b) sto-b)]
          [else (error 'interp "not a box")])])]
    [(setboxE b val)
     (type-case Result (interp b env sto)
       [(v*s v-b sto-b)
        (type-case Value v-b
          [(boxV l)
           (type-case Result (interp val env sto-b)
             [(v*s v-val sto-val)
              (v*s v-val (override-store (cell l v-val) sto-val))])]
          [else (error 'interp "not a box")])])]
    [(beginE l r)
     (type-case Result (interp l env sto)
       [(v*s v-l sto-l) (interp r env sto-l)])]))

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

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))
