; Cours 10 : Types

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
  [lamE (par : Symbol) (par-type : Type) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [boolE (b : Boolean)]
  [ifE (cnd : Exp) (fst : Exp) (snd : Exp)]
  [equalE (fst : Exp) (snd : Exp)]
  [pairE (fst : Exp) (snd : Exp)]
  [fstE (body : Exp)]
  [sndE (body : Exp)]
  [letrecE (name : Symbol) (t : Type) (expr : Exp) (body : Exp)])

;[letrecE (args : (Listof (Symbol * (Type * Exp)))) (body : Exp)]
; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [arrowT (par : Type) (res : Type)]  
  [prodT (l : Type) (r : Type)])
   
; Représentation des liaisons identificateurs type
(define-type TypeBinding
  [tbind (name : Symbol) (type : Type)])

; Environnement pour les types
(define-type-alias TypeEnv (Listof TypeBinding))

(define-type Thunk
  [delay (e : Exp) (env : Env) (mem : (Boxof (Optionof Value)))]
  [undef])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [boolV (b : Boolean)]
  [pairV (fst : Thunk) (snd : Thunk)]
  [undefV])

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

(define (compose f g)
  (lambda (x) (f (g x))))

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `true s) (boolE #t)]
    [(s-exp-match? `false s) (boolE #f)]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{letrec {[SYMBOL : ANY ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (letrecE
          (s-exp->symbol (first sll))
          (parse-type (third sll))
          (parse (fourth sll))
          (parse (third sl)))))]
    [(s-exp-match? `{= ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (equalE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{pair ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))]
    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (lamE (s-exp->symbol (first sll))
               (parse-type (third sll))
               (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL : ANY ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (appE
          (lamE (s-exp->symbol (first sll))
                (parse-type (third sll))
                (parse (third sl)))
          (parse (fourth sll)))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type
  (cond
    [(s-exp-match? `num s) (numT)]
    [(s-exp-match? `bool s) (boolT)]
    [(s-exp-match? `(ANY -> ANY) s)
     (let ([sl (s-exp->list s)])
       (arrowT (parse-type (first sl))
               (parse-type (third sl))))]
    [(s-exp-match? `(ANY * ANY) s)
     (let ([sl (s-exp->list s)])
       (prodT (parse-type (first sl)) (parse-type (third sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(multE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg)
     (let ([t1 (typecheck fun env)]
           [t2 (typecheck arg env)])
       (type-case Type t1
         [(arrowT par-type res-type)
          (if (equal? par-type t2)
              res-type
              (type-error arg par-type t2))]
         [else (type-error-function fun t1)]))]
    [(boolE t) (boolT)]
    [(ifE cnd fst snd)
     (let ([t0 (typecheck cnd env)])
       (type-case Type t0
         [(boolT) (let ([t1 (typecheck fst env)]
                        [t2 (typecheck snd env)])
                    (if (equal? t1 t2)
                        t1
                        (type-error fst t1 t2)))]
         [else (type-error cnd (boolT) t0)]))]
    [(equalE fst snd) (let ([t1 (typecheck fst env)]
                            [t2 (typecheck snd env)])
                        (if (equal? t1 t2)
                            (boolT)
                            (type-error fst t1 t2)))]
    [(pairE fst snd) (let ([t1 (typecheck fst env)]
                           [t2 (typecheck snd env)])
                       (prodT t1 t2))]
    [(fstE body)
     (let ([t (typecheck body env)])
       (type-case Type t
         [(prodT l r) l]
         [else (type-error-product body t)]))]
    [(sndE body) (let ([t (typecheck body env)])
                   (type-case Type t
                     [(prodT l r) r]
                     [else (type-error-product body t)]))]
    [(letrecE name t expr body)
     (let ([new-env (extend-env (tbind name t) env)])
       (let ([t-expr (typecheck expr new-env)]
             [t-body (typecheck body new-env)])
         (begin
           (display t)
           (display "\n")
           (display t-expr)
           (display "\n")
           (display t-body)
           (display "\n")
           (if (equal? t t-expr)
               t-body
               (type-error body t-expr t)))))]))
                                  

; Concaténation de chaînes de caractères
(define (cat [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Message d'erreur
(define (type-error [expr : Exp] [expected-type : Type] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected type " (to-string expected-type)
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-function [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected function "
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-product [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected product "
                               ", found type " (to-string found-type)))))

; Recherche d'un identificateur dans l'environnement
(define (type-lookup [s : Symbol] [env : TypeEnv]) : Type
  (cond
    [(empty? env) (error 'typecheck "free identifier")]
    [(equal? s (tbind-name (first env))) (tbind-type (first env))]
    [else (type-lookup s (rest env))]))

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
    [(lamE par par-type body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(boolE b) (boolV b)]
    [(ifE cnd fst snd) (if (equal? (interp cnd env) (boolV #t))
                           (interp fst env)
                           (interp snd env))]
    [(equalE fst snd) (if (equal? (interp fst env) (interp snd env))
                          (boolV #t)
                          (boolV #f))]
    [(pairE fst snd)
     (pairV (delay fst env (box (none))) (delay snd env (box (none))))]
    [(fstE e) (type-case Value (interp e env)
                [(pairV f s) (force f)]
                [else (error 'interp "not a pair")])]
    [(sndE e) (type-case Value (interp e env)
                [(pairV f s) (force s)]
                [else (error 'interp "not a pair")])]
    [(letrecE name t expr body)
     (letrec ([new-env (extend-env (bind name val) env)]
              [val (interp expr new-env)])
       (interp body env))]))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol]
                [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
    [else (lookup s (rest env))]))

(define (force [t : Thunk]) : Value
  (type-case Thunk t
    [(delay e env mem)
     (type-case (Optionof Value) (unbox mem)
       [(none) (begin
                 (set-box! mem (some (undefV)))
                 (let ([val (interp e env)])
                     (begin
                       (set-box! mem (some val))
                       val)))]
       [(some val) val])]
    [(undef) (undefV)]))

; Vérification des types pour les opérations arithmétiques
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

; Spécialisation de num-op pour l'addition
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

; Spécialisation de num-op pour la multiplication
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (let ([expr (parse e)])
    (begin
      (typecheck expr mt-env)
      (interp expr mt-env))))

(define (typecheck-expr [e : S-Exp]) : Type
  (typecheck (parse e) mt-env))

( test ( typecheck-expr `{ if {= 1 2} true false })
       ( boolT ))
( test/exn ( typecheck-expr `{ if 1 2 3})
           "typecheck")
( test ( typecheck-expr `{ pair 1 true }) ( prodT ( numT ) ( boolT )))
( test ( typecheck-expr `{ fst { pair 1 true } }) ( numT ))
( test ( typecheck-expr `{ snd { pair 1 true } }) ( boolT ))
( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })
       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))
( test ( typecheck-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       ( numT ))
( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       ( numV 5))