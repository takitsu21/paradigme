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
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [unletE (s : Symbol) (body : Exp)]
  [delayE (body : Exp)]
  [forceE (body : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [boolV (b : Boolean)]
  [thunkV (t : Exp) (env : Env)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (z s)
  (cond
    [(s-exp-match? `{delay ANY} s)
     (let ([sl (s-exp->list s)])
       (delayE (parse (second sl))))]
    [(s-exp-match? `{force ANY} s)
     (let ([sl (s-exp->list s)])
       (forceE (parse (second sl))))]
    [else (error 'z "erreur")]))

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;
(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `{delay ANY} s)
     (let ([sl (s-exp->list s)])
       (delayE (parse (second sl))))]
    [(s-exp-match? `{force ANY} s)
     (let ([sl (s-exp->list s)])
       (forceE (parse (second sl))))]
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (if (equal? s `true)
                                  (boolE #t)
                                  (if (equal? s `false)
                                      (boolE #f)
                                      (idE (s-exp->symbol s))))]
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
    [(s-exp-match? `{unlet SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (unletE (s-exp->symbol (second sl)) (parse (third sl))))]
    
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    
    [else (error 'parse "invalid input")]))


;[(unletE s body) (if (> 2 (length env))
;                     (error 'interp "free identifier")
;                     (bind-val (second env)))]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

(define (delete-item acc item l mt)
  (cond
    [(or (empty? l) (equal? #t acc)) (append mt l)]
    [(equal? item (bind-name (first l))) (delete-item #t item (rest l) mt)]
    [else (delete-item acc item (rest l) (append mt (list (first l))))]))

#;(define (thunk-all env mt) : Env
    (cond
      [(empty? env) mt]
      [(equal? 'delay (bind-name (first env))) (thunk-all (rest env) (append mt (list (bind (bind-name (first env)) (thunkV (bind-val (first env)))))))]
      [else (thunk-all (rest env) (append mt (list (first env))))]))

(define (force-env env mt) : Env
  (cond
    [(empty? env) mt]
    [(equal? 'delay (bind-name (first env))) (force-env (rest env) (append mt (list (first env))))]
    [else (force-env (rest env) (append mt (list (first env))))]))

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(boolE b) (boolV b)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(equalE l r) (num= (interp l env) (interp r env))]
    [(lamE par body) (closV par body env)]
    [(ifE first second third) (eval-if first second third env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(letE s rhs body) (interp body (extend-env (bind s (interp rhs env)) env))]
    [(forceE body)
     (type-case Value (interp body env)
       [(thunkV e c-env)
        (interp e c-env)]
       [else (error 'interp "not a thunk")])]
    [(delayE body) (thunkV body env)]
    
    [(unletE s body)
     (interp body (delete-item #f s env empty))]))



(define (eval-if [first : Exp]
                 [second : Exp]
                 [third : Exp]
                 [env : Env]) : Value
  (let ([if-val (interp first env)])
    (if (not (boolV? if-val))
        (error 'interp "not a boolean")
        (if (boolV? if-val)
            (interp second env)
            (interp third env)))))

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
(test (interp-expr `{ let {[x 1]} {let {[x 2]} {unlet x x}}}) (numV 1))
(test (interp-expr `{ let {[x 1]}
                       { let {[x 2]}
                          {+ { unlet x x} x} } }) (numV 3))
(test/exn (interp-expr `{ let {[x 1]}
                           { unlet x x} }) "free identifier")
(test/exn (interp-expr `{ let {[x 1]}
                           { let {[y 2]}
                              {let {[x 3]}
                                {let {[x 4]}
                                  {+ { unlet x {unlet y y}} x}}}}}) "free identifier")
(test (interp-expr `{ let {[y 1]}
                       { let {[y 2]}
                          {let {[x 3]}
                            {let {[x 4]}
                              {+ { unlet x {unlet y y}} x}}}}}) (numV 5))
(test/exn (interp-expr `{ delay {+ 1 { lambda {x} x} } }) "pas d'erreur")
(test/exn (interp-expr `{ force { delay {+ 1 { lambda {x} x} } } }) "not a number")
(test (interp-expr `{ let {[t { let {[x 1]} { delay x} }]}
                       { let {[x 2]}
                          { force t} } }) (numV 1))
(test (interp-expr `{force {delay {force {delay {+ 3 1}}}}}) (numV 4))
(test (interp-expr `{force {delay {+ 3 1}}}) (numV 4))
(test (interp-expr `{force {delay { let {[t { let {[x 1]} { delay x} }]}
                       { let {[x 2]}
                          { force t} } }}}) (numV 1))