; Cours 05 : Les variables

#lang plait

;;;;;;;;;
; Macro ;
;;;;;;;;;

(define-syntax-rule (with [(v-id sto-id) call] body)
  (type-case Result call
    [(v*s v-id sto-id) body]))

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
  [setE (s : Symbol) (val : Exp)]
  [beginE (l : Exp) (r : Exp)]
  [addressE (var : Symbol)]
  [contentE (loc : Exp)]
  [set-contentE (loc : Exp) (expr : Exp)]
  [mallocE (expr : Exp)]
  [freeE (expr : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (location : Location)])

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
( define-type Store
   [ store ( storages : ( Listof Storage ))
           ( pointers : ( Listof Pointer ))])


( define-type Pointer
   [ pointer (loc : Location ) ( size : Number )])

(define mt-store
  (store empty empty))
(define (override-store x sto)
  (store (cons x (store-storages sto)) (store-pointers sto)))

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
    [(s-exp-match? `{set! SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (s-exp->symbol (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{address SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (addressE (s-exp->symbol (second sl))))]
    [(s-exp-match? `{content ANY} s)
     (let ([sl (s-exp->list s)])
       (contentE (parse (second sl))))]
    [(s-exp-match? `{set-content! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (set-contentE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{malloc ANY} s)
     (let ([sl (s-exp->list s)])
       (mallocE (parse (second sl))))]
    [(s-exp-match? `{free ANY} s)
     (let ([sl (s-exp->list s)])
       (freeE (parse (second sl))))]
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
    [(idE s) (v*s (fetch (lookup s env) sto) sto)]
    [(plusE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num+ v-l v-r) sto-r)))]
    [(multE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num* v-l v-r) sto-r)))]
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (with [(v-f sto-f) (interp f env sto)]
           (type-case Value v-f
             [(closV par body c-env)
              (type-case Exp arg
                [(idE s) (interp body
                                 (extend-env (bind par (lookup s env)) c-env)
                                 sto-f)]
                [else (with [(v-arg sto-arg) (interp arg env sto-f)]
                            (let ([l (new-loc sto-arg)])
                              (interp body
                                      (extend-env (bind par l) c-env)
                                      (override-store (cell l v-arg) sto-arg))))])]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (let ([l (new-loc sto-rhs)])
             (interp body
                     (extend-env (bind s l) env)
                     (override-store (cell l v-rhs) sto-rhs))))]
    [(setE var val)
     (let ([l (lookup var env)])
       (with [(v-val sto-val) (interp val env sto)]
             (v*s v-val (override-store (cell l v-val) sto-val))))]
    [(beginE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (interp r env sto-l))]
    [(addressE var) (v*s (numV (lookup var env)) sto)]
    [(contentE loc)
     (with [(v-b sto-b) (interp loc env sto)]
           (if (integer? (numV-n v-b))
               (v*s (fetch (numV-n v-b) sto-b) sto-b)
               (error 'interp "segmentation fault")))]
    [(set-contentE loc expr) (with [(v-b sto-b) (interp loc env sto)]
                                   (if (integer? (numV-n v-b))
                                       (with [(v-c sto-c) (interp expr env sto-b)]
                                             (v*s v-c (override-store (cell (numV-n v-b) v-c) sto-c)))
                                       (error 'interp "segmentation fault")))]
    [(mallocE expr) (with [(v-b sto-b) (interp expr env sto)]
                          (if (and (numV? v-b) (integer? (numV-n v-b)) (>= (numV-n v-b) 0))
                              (malloc-dyn (numV-n v-b) sto-b (numV-n v-b) empty)
                              (error 'interp "not a size")))]
    [(freeE expr)
     (if (empty? (store-pointers sto))
         (error 'interp "not an allocated pointer")
         (with [(v-b sto-b) (interp expr env sto)]
               (begin
                 (display "to")
                 (display (pointer-loc (first (store-pointers sto-b))))
                 (display "\nfrom")
                 (display (cell-location (first (store-storages sto-b))))
                 (display "\n")
               (v*s (numV 0) (free-aux (store-pointers sto-b) (store-storages sto-b) empty (pointer-loc (first (store-pointers sto-b)))
                                       (cell-location (first (store-storages sto-b))))))))]))



(define (free-aux pointers storages acc to from)
  (cond
    [(empty? storages) (store acc (rest pointers))]
    [(and (>= from to) (equal? 0 (numV-n (cell-val (first storages)))))
     (free-aux pointers (rest storages) acc to (- from 1))]
    [(= from to) (free-aux pointers (rest storages) (cons (first storages) acc) (pointer-size (first pointers)) (cell-location (first storages)))]
    [else (begin
            (free-aux pointers (rest storages) (cons (first storages) acc) to (- from 1)))]))

(define (malloc-dyn n sto start alloc)
  (if (= n 0)
      (let [(alloc-reversed (reverse alloc))]
        (v*s (numV (first alloc-reversed)) (store (store-storages sto) (cons (pointer (first alloc-reversed) start) (store-pointers sto)))))
      (let [(l (new-loc sto))]
        (malloc-dyn (- n 1) (override-store (cell l (numV 0)) sto) start (cons l alloc)))))

(define (integer? n) (= n (floor n)))

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
  (+ (max-address (store-storages sto)) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : (Listof Storage)]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? (store-storages sto)) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first (store-storages sto)))) (cell-val (first (store-storages sto)))]
    [else (fetch l (store (rest (store-storages sto)) (store-pointers sto)))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))

(test (interp-expr `{let {[x 0]} {address x}}) (numV 1))
(test (interp-expr `{let {[x 0]} {content 1}}) (numV 0))
(test (interp-expr `{let {[x 0]}
                      {begin {set-content! 1 2}
                             x}})
      (numV 2))

(test (interp-expr `{let [{x 0}]
                      {set-content! {set! x 1} {+ x 1}}})
      (numV 2))


( test/exn (interp-expr `{ let {[p { malloc -3}]} p})
           "not a size")

( test ( interp ( parse `{ let {[p { malloc 3}]} { free p} })
                mt-env
                mt-store )
       (v*s ( numV 0) ( store ( list ( cell 4 ( numV 1)))
                              empty )))

( test ( interp ( parse `{ let {[p { malloc 3}]} p}) mt-env mt-store )
       (v*s ( numV 1) ( store ( list ( cell 4 ( numV 1))
                                     ( cell 3 ( numV 0))
                                     ( cell 2 ( numV 0))
                                     ( cell 1 ( numV 0)))
                              ( list ( pointer 1 3)))))

( test/exn ( interp ( parse `{ let {[p { malloc 3}]}
                                {begin
                                  {free p}
                                  {free p}}})
                    mt-env
                    mt-store )
           "not an allocated pointer")
( test ( interp ( parse `{ let {[p { malloc 3}]}
                            {let {[c {malloc 4}]}
                              {let {[a {malloc 5}]}
                                {begin
                                  {free p}
                                  {free a}}}}})
                mt-env
                mt-store )
       (v*s (numV 0) (store (list
                             (cell 12 (numV 10))
                             (cell 9 (numV 5))
                             (cell 4 (numV 1))
                             (cell 3 (numV 0))
                             (cell 2 (numV 0))
                             (cell 1 (numV 0)))
                            (list (pointer 1 3)))))
(test/exn (interp-expr `{let {[a {malloc 8}]}
                          {free z}})
          "not an allocated pointer")