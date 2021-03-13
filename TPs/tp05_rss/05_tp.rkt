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
  [contentE (ptr : Exp)]
  [setcontentE (ptr : Exp) (val : Exp)]
  [mallocE (size : Exp)]
  [freeE (ptr : Exp)])

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
(define-type Store
  [store (storages : (Listof Storage)) (pointers : (Listof Pointer))])
(define mt-store (store empty empty))
(define (override-store c sto)
  (store (cons c (store-storages sto)) (store-pointers sto)))
(define-type Pointer
  [pointer (loc : Location) (size : Number)])

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
       (setcontentE (parse (second sl)) (parse (third sl))))]
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
    [(contentE ptr)
     (with [(v-ptr sto-ptr) (interp ptr env sto)]
           (type-case Value v-ptr
             [(numV loc) (v*s (fetch loc sto-ptr) sto-ptr)]
             [else (error 'interp "segmentation fault")]))]
    [(setcontentE ptr val)
     (with [(v-ptr sto-ptr) (interp ptr env sto)]
           (type-case Value v-ptr
             [(numV loc)
              (if (positive-integer? loc)
                  (with [(v-val sto-val) (interp val env sto-ptr)]
                        (v*s v-val (override-store (cell loc v-val) sto-val)))
                  (error 'interp "segmentation fault"))]
             [else (error 'interp "segmentation fault")]))]
    [(mallocE size)
     (with [(v-size sto-size) (interp size env sto)]
           (type-case Value v-size
             [(numV n) (if (positive-integer? n)
                           (let ([loc (new-loc sto-size)])
                             (v*s (numV loc) (add-pointer loc n (init-cells n loc sto-size))))
                           (error 'interp "not a size"))]
             [else (error 'interp "not a size")]))]
    [(freeE ptr)
     (with [(v-ptr sto-ptr) (interp ptr env sto)]
           (type-case Value v-ptr
             [(numV loc) (v*s (numV 0) (remove-pointer loc sto-ptr))]
             [else (error 'interp "not an allocated pointer")]))]))

; Prédicat pour les entiers strictement positifs
(define (positive-integer? [n : Number]) : Boolean
  (and (> n 0) (= n (floor n))))

; Renvoie un état de la mémoire où l'on a ajouté nb cellule à partir de l'adresse loc
(define (init-cells [n : Number] [loc : Location] [sto : Store]) : Store
  (if (= n 0)
      sto
      (init-cells (- n 1) loc (override-store (cell (new-loc sto) (numV 0)) sto))))

; Ajoute un pointeur à la liste des pointeurs de sto
(define (add-pointer [loc : Location] [size : Number] [sto : Store]) : Store
  (store (store-storages sto) (cons (pointer loc size) (store-pointers sto))))

(define (remove [e : 'a] [l : (Listof 'a)]) : (Listof 'a)
  (cond
    [(empty? l) l]
    [(equal? (first l) e) (rest l)]
    [else (cons (first l) (remove e (rest l)))]))

; Renvoie un pointeur associé à une adresse
(define (find-pointer [loc : Location] [pointers : (Listof Pointer)]) : Pointer
  (cond
    [(empty? pointers) (error 'interp "not an allocated pointer")]
    [(= (pointer-loc (first pointers)) loc) (first pointers)]
    [else (find-pointer loc (rest pointers))]))

; Retire un pointeur de la liste des pointeurs et supprime toutes les cellules associées
(define (remove-pointer [loc : Location] [sto : Store]) : Store
  (let ([ptr (find-pointer loc (store-pointers sto))])
    (type-case Pointer ptr
      [(pointer loc size)
       (store (filter (lambda (c)
                        (or (< (cell-location c) loc)
                            (>= (cell-location c) (+ loc size))))
                      (store-storages sto))
              (remove ptr (store-pointers sto)))])))

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
  (local [(define (fetch-aux [storages : (Listof Storage)]) : Value
            (cond
              [(empty? storages) (error 'interp "segmentation fault")]
              [(equal? l (cell-location (first storages))) (cell-val (first storages))]
              [else (fetch-aux (rest storages))]))]
    (fetch-aux (store-storages sto))))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))
