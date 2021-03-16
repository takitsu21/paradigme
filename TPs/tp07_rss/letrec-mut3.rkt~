; Cours 07 : letrec par mutation

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
  [letrecE (s : (Listof Symbol)) (rhs : (Listof Exp)) (body : Exp)]
  [ifE (cnd : Exp) (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [pairE (fst : Exp) (snd : Exp)]
  [fstE  (body : Exp)]
  [sndE (body : Exp)])



; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [undefV]
  [pairV (fst : Thunk) (snd : Thunk)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : (Boxof Thunk))])

(define-type Thunk
  [delay (e : Exp) (env : Env) (mem : (Boxof (Optionof Value)))]
  [undef])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;



(define (compose f g)
  (lambda (x) (f (g x))))

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
    [(s-exp-match? `{letrec {[SYMBOL ANY] [SYMBOL ANY] ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (map s-exp->list (s-exp->list (second sl)))])
         (letrecE (map (compose s-exp->symbol first) subst)
                  (map (compose parse second) subst)
                  (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (second sl))])
         (lamE (s-exp->symbol (first sll)) (parse (third sl)))))]
    [(s-exp-match? `{pair ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))]
    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;



(define (find-box s env)
  (cond
    [(empty? env) (box (undef))]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
    [else (find-box s(rest env))]))

(define (bind-all s env)
  (if (empty? s)
      env
      (bind-all (rest s) (extend-env (bind (first s) (box (undef))) env))))

(define (set-all-box s rhs body env)
  (if (empty? rhs)
      (interp body env)
      (begin
        (set-box! (find-box (first s) env) (delay (first rhs) env (box (some (interp (first rhs) env)))))
        (set-all-box (rest s) (rest rhs) body env))))


;(define (letrec-aux s rhs env)
;  (if (empty? s)
;      env
;        (letrec ([new-env (extend-env (bind (first s) (box (val))) env)]
;                 [val (delay (first rhs) env (box (some (interp (first rhs) env))))])
;          (interp body new-env))
;          
;          (begin
;            (letrec-aux (rest s) (rest rhs) new-env))))))

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (force (lookup s env))]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(letrecE s rhs body) (set-all-box s rhs body (bind-all s env))]
    [(ifE cnd l r)
     (type-case Value (interp cnd env)
       [(numV n) (if (not (= n 0)) (interp l env) (interp r env))]
       [else (error 'interp "not a number")])]
    [(lamE par body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (box (delay arg env (box (some (interp arg env)))))) c-env))]
       [else (error 'interp "not a function")])]
    [(pairE fst snd)
     (pairV (delay fst env (box (none))) (delay snd env (box (none))))]
    [(fstE e) (type-case Value (interp e env)
                [(pairV f s) (force f)]
                [else (error 'interp "not a pair")])]
    [(sndE e) (type-case Value (interp e env)
                [(pairV f s) (force s)]
                [else (error 'interp "not a pair")])]))

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

(define (force [t : Thunk]) : Value
  (type-case Thunk t
    [(delay e env mem)
     (type-case (Optionof Value) (unbox mem)
       [(none) (let ([val (interp e env)])
                 (begin
                   (set-box! mem (some val))
                   val))]
       [(some val) val])]
    [(undef) (undefV)]))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Thunk
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (unbox (bind-val (first env)))]
    [else (lookup n (rest env))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))

(interp-expr `{letrec {[x x]} x})
( test ( interp-expr
         `{ letrec {[ numbers-from { lambda {n}
                                      { pair n
                                             { numbers-from {+ n 1} } } }]}
             { let {[ ints { numbers-from 0}]}
                { fst { snd { snd { snd ints } } } } } })
       ( numV 3))


( test ( interp-expr
         `{ letrec {[even? {lambda {n} {if n
                                           {odd? {- n 1} }
                                           1}}]
                    [odd? {lambda {n} {if n
                                          {even? {- n 1} }
                                          0} }]}
             { even? 5} })
       (numV 0))

( test ( interp-expr
         `{ letrec {[even? {lambda {n} {if n
                                           {odd? {- n 1} }
                                           1}}]
                    [odd? {lambda {n} {if n
                                          {even? {- n 1} }
                                          0} }]}
             { odd? 15} })
       (numV 1))


( test ( interp-expr
         `{ letrec
               {; curryfied map2 on infinite lists
                [map2 { lambda {f}
                         { lambda {l1}
                            { lambda {l2}
                               { pair { {f { fst l1} } { fst l2} }
                                      { { { map2 f} { snd l1} } { snd l2} } } } } }]
                ; curryfied list-ref
                [list-ref { lambda {l}
                             { lambda {n}
                                { if n
                                     { { list-ref { snd l} } {- n 1} }
                                     { fst l} } } }]
                ; curryfied addition function
                [add { lambda {x} { lambda {y} {+ x y} } }]
                ; infinite fibonacci sequence !!!
                ; ( list 0 1 1 2 3 5 8 13 ... )
                [ fibo { pair 0
                              { pair 1
                                     { { { map2 add } fibo } { snd fibo } } } }]}
             { { list-ref fibo } 7} })
       ( numV 13))
