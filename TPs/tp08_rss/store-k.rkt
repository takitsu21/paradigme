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
  [lamE (par : Symbol) (body : Exp)]
  [let/ccE (s : Symbol) (body : Exp)]
  [setE (par : Symbol) (body : Exp)]
  [beginE (l : Exp) (r : Exp)]
  [ifE (cnd : Exp) (l : Exp) (r : Exp)]
  [whileE (cnd : Exp) (body : Exp)]
  [breakE])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [contV (k : Cont)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (location : Location)])

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
  [setK (par : Location) (env : Env) (k : Cont)]
  [beginK (r : Exp) (env : Env) (k : Cont)]
  [ifK (l : Exp) (r : Exp) (env : Env) (k : Cont)]
  [doWhileK (cnd : Exp) (body : Exp) (env : Env) (k : Cont)]
  [whileFirstK (val : Value) (cnd : Exp) (body : Exp) (env : Env) (k : Cont)])

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
    [(s-exp-match? `break s) (breakE)]
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
    [(s-exp-match? `{let/cc SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (let/ccE (s-exp->symbol (second sl)) (parse (third sl))))]
    [(s-exp-match? `{while ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (whileE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{set! SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (s-exp->symbol (second sl)) (parse (third sl))))]
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
(define (interp [e : Exp] [env : Env] [sto : Store] [k : Cont]) : Value
  (type-case Exp e
    [(numE n) (continue k (numV n) sto)]
    [(idE s) (continue k (fetch (lookup s env) sto) sto)]
    [(plusE l r) (interp l env sto (addSecondK r env k))]
    [(multE l r) (interp l env sto (multSecondK r env k))]
    [(lamE par body) (continue k (closV par body env) sto)]
    [(appE f arg) (interp f env sto (appArgK arg env k))]
    [(let/ccE s body)
     (let ([l (new-loc sto)])
       (interp body
               (extend-env (bind s l) env)
               (override-store (cell l (contV k)) sto)
               k))]
    [(beginE l r)
     (interp l env sto (beginK r env k))]
    [(setE par body)
     (let ([l (lookup par env)])
       (interp body env sto (setK l env k)))]
    [(ifE cnd l r)
     (interp cnd env sto (ifK l r env k))]
    [(whileE cnd body) (interp cnd env sto (whileFirstK (numV 0) cnd body env k))]
    [(breakE) (type-case Cont k
                [(whileFirstK v cnd body env next-k) (if (breakE? cnd)
                                                         (error 'interp "break outside while")
                                                         (continue next-k (numV 0) sto))]
                [(doWhileK cnd body env next-k) (continue next-k (numV 0) sto)]
                [else (error 'interp "break outside while")])]))

; Appel des continuations
(define (continue [k : Cont] [val : Value] [sto : Store]) : Value
  (type-case Cont k
    [(doneK) val]
    [(addSecondK r env next-k) (interp r env sto (doAddK val next-k))]
    [(doAddK v-l next-k) (continue next-k (num+ v-l val) sto)]
    [(multSecondK r env next-k) (interp r env sto (doMultK val next-k))]
    [(doMultK v-l next-k) (continue next-k (num* v-l val) sto)]
    [(appArgK arg env next-k) (interp arg env sto (doAppK val next-k))]
    [(doAppK v-f next-k)
     (type-case Value v-f
       [(closV par body c-env)
        (let ([l (new-loc sto)])
          (interp body
                  (extend-env (bind par l) c-env)
                  (override-store (cell l val) sto)
                  next-k))]
       [(contV k-v) (continue k-v val sto)]
       [else (error 'interp "not a function")])]
    [(setK l env next-k)
     (continue next-k val (override-store (cell l val) sto))]
    [(beginK r env next-k) (interp r env sto next-k)]
    [(ifK l r env next-k) (type-case Value val
                            [(numV n) (if (= 0 n)
                                          (interp r env sto next-k)
                                          (interp l env sto next-k))]
                            [else (error 'continue "not a number")])]
    
    [(whileFirstK v-f cnd body env next-k)
     (if (equal? val (numV 0))
         (continue next-k v-f sto)
         (interp body env sto (doWhileK cnd body env next-k)))]
    [(doWhileK cnd body env next-k) 
     (interp cnd env sto (whileFirstK val cnd body env next-k))]))


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
(define (lookup [n : Symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-location (first env))]
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
  (interp (parse e) mt-env mt-store (doneK)))

( test ( interp-expr `{ let {[x 0]}
                         { begin { set! x 1}
                                 x} })
       ( numV 1))
( test ( interp-expr `{ if 1 2 3}) ( numV 2))
( test ( interp-expr `{ if 0 2 3}) ( numV 3))
( test ( interp-expr `{ while 0 x}) ( numV 0))
( test ( interp-expr `{ let {[fac
                              { lambda {n}
                                 { let {[res 1]}
                                    { begin
                                       { while n ; tant que n est non nul
                                               { begin
                                                  { set! res {* n res } }
                                                  { set! n {+ n -1} } } }
                                       
                                       res } } }]}
                         { fac 6} })
       ( numV 720))
(test (interp-expr `{let {[x 1]}
                      {begin
                        {while 0 {set! x 2}}
                        x}})
      (numV 1))

(test (interp-expr `{let {[x 1]}
                      {begin
                        {while 0 0}
                        x}})
      (numV 1))

( test ( interp-expr `{ while 1 break }) ( numV 0))
( test/exn ( interp-expr ` break ) "break outside while")
( test/exn ( interp-expr `{ while break 1}) "break outside while")
( test ( interp-expr `{ let {[n 10]}
                         { begin
                            { while n ; tant que n est non nul
                                    { if {- n 5}
                                         { set! n {- n 1} } ; si n n' egale pas 5
                                         break } } ; si n egale 5
                            n} })
       ( numV 5))