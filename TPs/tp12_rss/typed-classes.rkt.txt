; Cours 12 : Types et classes

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des classes (langage utilisateur typé)
(define-type ClassT
  [classT (super-name : Symbol)
          (fields : (Listof (Symbol * Type)))
          (methods : (Listof (Symbol * MethodT)))])

; Représentation des méthodes (langage utilisateur typé)
(define-type MethodT
  [methodT (arg-type : Type)
           (res-type : Type)
           (body : ExpS)])

; Représentation des types
(define-type Type
  [numT]
  [objT (class-name : Symbol)])

; Représentation des classes (langage utilisateur non typé)
(define-type ClassS
  [classS (super-name : Symbol)
          (field-names : (Listof Symbol))
          (methods : (Listof (Symbol * ExpS)))])

; Représentation des expressions (langage utilisateur)
(define-type ExpS
  [thisS]
  [argS]
  [numS (n : Number)]
  [plusS (l : ExpS)
         (r : ExpS)]
  [multS (l : ExpS)
         (r : ExpS)]
  [newS (class : Symbol)
        (field-values : (Listof ExpS))]
  [getS (object : ExpS)
        (field : Symbol)]
  [sendS (object : ExpS)
         (method : Symbol)
         (arg : ExpS)]
  [superS (method : Symbol)
          (arg : ExpS)])

; Représentation des classes (langage interne)
(define-type Class
  [classE (field-names : (Listof Symbol))
          (methods : (Listof (Symbol * Exp)))])

; Représentation des expressions (langage interne)
(define-type Exp
  [thisE]
  [argE]
  [numE (n : Number)]
  [plusE (l : Exp)
         (r : Exp)]
  [multE (l : Exp)
         (r : Exp)]
  [newE (class : Symbol)
        (field-values : (Listof Exp))]
  [getE (object : Exp)
        (field : Symbol)]
  [sendE (object : Exp)
         (method : Symbol)
         (arg : Exp)]
  [ssendE (object : Exp)
          (class : Symbol)
          (method : Symbol)
          (arg : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [objV (class-name : Symbol)
        (field-values : (Listof Value))])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

; Retourne le cinquième élément d'une liste
(define (fifth [l : (Listof 'a)]) : 'a
  (list-ref l 4))

; Supprime les premiers éléments d'une liste
(define (drop [l : (Listof 'a)] [n : Number]) : (Listof 'a)
  (if (= n 0)
      l
      (drop (rest l) (- n 1))))

; Analyse d'une classe
(define (parse-class [s : S-Exp]) : (Symbol * ClassT)
  (cond
    [(s-exp-match?
      `{class SYMBOL extends SYMBOL
         {[SYMBOL : ANY] ...}
         {SYMBOL {[arg : ANY]} : ANY ANY} ...}
      s)
     (let* ([sl (s-exp->list s)]
            [class-name (s-exp->symbol (second sl))]
            [super-name (s-exp->symbol (fourth sl))]
            [fds (map parse-field (s-exp->list (fifth sl)))]
            [mtds (map parse-method (drop sl 5))])
       (pair class-name (classT super-name fds mtds)))]
    [else (error 'parse "invalid input")]))

; Analyse d'un champ
(define (parse-field [s : S-Exp]) : (Symbol * Type)
  (let ([sl (s-exp->list s)])
    (pair
     (s-exp->symbol (first sl))
     (parse-type (third sl)))))

; Analyse d'une méthode
(define (parse-method [s : S-Exp]) : (Symbol * MethodT)
  (let* ([sl (s-exp->list s)]
         [arg-types (s-exp->list (second sl))])
    (pair
     (s-exp->symbol (first sl))
     (methodT
      (parse-type (third (s-exp->list (first arg-types))))
      (parse-type (fourth sl))
      (parse (fifth sl) #t)))))

; Analyse d'un type
(define (parse-type [s : S-Exp]) : Type
  (cond
    [(s-exp-match? `num s) (numT)]
    [(s-exp-match? `SYMBOL s) (objT (s-exp->symbol s))]
    [else (error 'parse "invalid input")]))

; Analyse des expressions
(define (parse [s : S-Exp] [in-method : Boolean]) : ExpS
  (local [(define (parse-r s) (parse s in-method))]
    (cond
      [(s-exp-match? `arg s)
       (if in-method
           (argS)
           (error 'parse "invalid input"))]
      [(s-exp-match? `this s)
       (if in-method
           (thisS)
           (error 'parse "invalid input"))]
      [(s-exp-match? `NUMBER s)
       (numS (s-exp->number s))]
      [(s-exp-match? `{+ ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (plusS
          (parse-r (second sl))
          (parse-r (third sl))))]
      [(s-exp-match? `{* ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (multS
          (parse-r (second sl))
          (parse-r (third sl))))]
      [(s-exp-match? `{new SYMBOL ANY ...} s)
       (let ([sl (s-exp->list s)])
         (newS
          (s-exp->symbol (second sl))
          (map parse-r (drop sl 2))))]
      [(s-exp-match? `{get ANY SYMBOL} s)
       (let ([sl (s-exp->list s)])
         (getS
          (parse-r (second sl))
          (s-exp->symbol (third sl))))]
      [(s-exp-match? `{send ANY SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (sendS
          (parse-r (second sl))
          (s-exp->symbol (third sl))
          (parse-r (fourth sl))))]
      [(s-exp-match? `{super SYMBOL ANY} s)
       (if in-method
           (let ([sl (s-exp->list s)])
             (superS
              (s-exp->symbol (second sl))
              (parse-r (third sl))))
           (error 'parse "invalid input"))]
      [else (error 'parse "invalid input")])))

;;;;;;;;;;
; Typage ;
;;;;;;;;;;

(define (typecheck
         [expr : ExpS]
         [classes : (Listof (Symbol * ClassT))]) : Type
  (begin
    (map (lambda (class)
           (typecheck-class class classes))
         classes)
    (typecheck-expr expr classes (objT 'Object) (numT))))

; Vérification de la définition d'une classe
(define (typecheck-class
         [class : (Symbol * ClassT)]
         [classes : (Listof (Symbol * ClassT))]) : Void
  (type-case ClassT (snd class)
    [(classT super-name fds mtds)
     (begin
       (map (lambda (mtd)
              (begin
                (typecheck-method (snd mtd) (objT (fst class)) classes)
                (check-override mtd class classes)))
            mtds)
       (void))]))

; Vérification de la définition d'une méthode
(define (typecheck-method
         [mtd : MethodT]
         [this-t : Type]
         [classes : (Listof (Symbol * ClassT))]) : Void
  (type-case MethodT mtd
    [(methodT arg-t res-t body)
     (let ([body-t (typecheck-expr body classes this-t arg-t)])
       (if (is-subtype? body-t res-t classes)
           (void)
           (type-error body res-t body-t)))]))

; Vérification de la cohérence d'une redéfinition de méthode
(define (check-override
         [mtd : (Symbol * MethodT)]
         [class : (Symbol * ClassT)]
         [classes : (Listof (Symbol * ClassT))]) : Void
  (let ([super-name (classT-super-name (snd class))])
    (type-case (Optionof MethodT) (find-method-in-ancestors
                                   (fst mtd)
                                   super-name
                                   classes)
      [(none) (void)]
      [(some super-mtd)
       (if (and (equal? (methodT-arg-type (snd mtd))
                        (methodT-arg-type super-mtd))
                (equal? (methodT-res-type (snd mtd))
                        (methodT-res-type super-mtd)))
           (void)
           (error 'typecheck (cat (list "bad override of method "
                                        (to-string (fst mtd))
                                        " in class "
                                        (to-string (fst class))))))])))

; Typage d'une expression
(define (typecheck-expr
         [expr : ExpS]
         [classes : (Listof (Symbol * ClassT))]
         [this-t : Type]
         [arg-t : Type]) : Type
  (let* ([typecheck-expr-r
          (lambda (expr)
            (typecheck-expr expr classes this-t arg-t))]
         [typecheck-op (lambda (l r)
                         (let ([t1 (typecheck-expr-r l)]
                               [t2 (typecheck-expr-r r)])
                           (if (numT? t1)
                               (if (numT? t2)
                                   (numT)
                                   (type-error r (numT) t2))
                               (type-error l (numT) t1))))]
         [check-type (lambda (expr t)
                       (let ([expr-t (typecheck-expr-r expr)])
                         (if (is-subtype? expr-t t classes)
                             (void)
                             (type-error expr t expr-t))))])
    (type-case ExpS expr
      [(thisS) this-t]
      [(argS) arg-t]
      [(numS n) (numT)]
      [(plusS l r) (typecheck-op l r)]
      [(multS l r) (typecheck-op l r)]
      [(newS class-name args)
       (let ([fds-types (map snd (extract-fields class-name classes))])
         (if (= (length args)
                (length fds-types))
             (begin
               (map2 check-type args fds-types)
               (objT class-name))
             (error 'typecheck "wrong fields count")))]
      [(getS obj fd-name)
       (let ([obj-t (typecheck-expr-r obj)])
         (type-case Type obj-t
           [(objT class-name)
            (find fd-name (extract-fields class-name classes))]
           [else (type-error-object obj obj-t)]))]
      [(sendS obj mtd-name arg)
       (let ([obj-t (typecheck-expr-r obj)]
             [new-arg-t (typecheck-expr-r arg)])
         (type-case Type obj-t
           [(objT class-name)
            (typecheck-send class-name mtd-name arg new-arg-t classes)]
           [else (type-error-object obj obj-t)]))]
      [(superS mtd-name arg)
       (let ([this-class (find (objT-class-name this-t) classes)]
             [new-arg-t (typecheck-expr-r arg)])
         (typecheck-send (classT-super-name this-class) mtd-name arg new-arg-t classes))])))

; Typage d'un appel de méthode
(define (typecheck-send
         [class-name : Symbol]
         [mtd-name : Symbol]
         [arg : ExpS]
         [arg-t : Type]
         [classes : (Listof (Symbol * ClassT))]) : Type
  (type-case (Optionof MethodT) (find-method-in-ancestors
                                 mtd-name
                                 class-name
                                 classes)
    [(none) (error 'typecheck "not found")]
    [(some mtd)
     (type-case MethodT mtd
       [(methodT arg-t-expected res-t body)
        (if (is-subtype? arg-t arg-t-expected classes)
            res-t
            (type-error arg arg-t-expected arg-t))])]))

; Retourne la liste des champs d'une classe
; Comme l'héritage n'est pas encore réalisé, il faut parcourir les classes parentes
(define (extract-fields
         [class-name : Symbol]
         [classes : (Listof (Symbol * ClassT))]) : (Listof (Symbol * Type))
  (letrec ([extract-fields-r
            (lambda (class-name acc)
              (if (equal? class-name 'Object)
                  acc
                  (type-case ClassT (find class-name classes)
                    [(classT super-name fds mtds)
                     (extract-fields-r super-name (append fds acc))])))])
    (extract-fields-r class-name empty)))

; Recherche d'une méthode dans une classe
; Comme l'héritage n'est pas encore réalisé, il faut parcourir les classes parentes
(define (find-method-in-ancestors
         [mtd-name : Symbol]
         [class-name : Symbol]
         [classes : (Listof (Symbol * ClassT))]) : (Optionof MethodT)
  (if (equal? class-name 'Object)
      (none)
      (let ([class (find class-name classes)])
        (type-case (Optionof MethodT) (find-opt mtd-name (classT-methods class))
          [(none) (find-method-in-ancestors
                   mtd-name
                   (classT-super-name class)
                   classes)]
          [(some mtd) (some mtd)]))))

; Prédicat pour la relation de sous-typage
(define (is-subtype?
         [t1 : Type]
         [t2 : Type]
         [classes : (Listof (Symbol * ClassT))]) : Boolean
  (type-case Type t1
    [(objT name1)
     (type-case Type t2       
       [(objT name2)
        (is-subclass? name1 name2 classes)]
       [else #f])]
    [else (equal? t1 t2)]))

; Prédicat pour la relation de sous-classe
(define (is-subclass?
         [name1 : Symbol]
         [name2 : Symbol]
         [classes : (Listof (Symbol * ClassT))])
  (cond
    [(equal? name1 name2) #t]
    [(equal? name1 'Object) #f]
    [else (is-subclass?
           (classT-super-name (find name1 classes))
           name2
           classes)]))

; Concaténation de chaînes de caractères
(define (cat [strings : (Listof String)]) : String
  (foldr string-append "" strings))
                  
; Message d'erreur
(define (type-error [expr : ExpS] [expected-type : Type] [found-type : Type])
  (error 'typecheck (cat (list "expression "
                               (to-string  expr)
                               ", expected type "
                               (to-string expected-type)
                               ", found type "
                               (to-string found-type)))))

; Message d'erreur
(define (type-error-object [expr : ExpS] [found-type : Type])
  (error 'typecheck (cat (list "expression "
                               (to-string  expr)
                               ", expected object, found type "
                               (to-string found-type)))))

; Effacement des types
(define (strip-types [typed-raw : ClassT]) : ClassS
  (type-case ClassT typed-raw
    [(classT super-name fds mtds)
     (classS
      super-name
      (map fst fds)
      (map (lambda (mtd)
             (pair
              (fst mtd)
              (methodT-body (snd mtd))))
           mtds))]))

;;;;;;;;;;;;;;;
; Compilation ;
;;;;;;;;;;;;;;;

; passage d'une expression utilisateur en expression interne
(define (exp-s->e [expr : ExpS] [super-name : Symbol]) : Exp
  (let ([aux (lambda (expr)
               (exp-s->e expr super-name))])
    (type-case ExpS expr
      [(thisS) (thisE)]
      [(argS) (argE)]
      [(numS n) (numE n)]
      [(plusS l r)
       (plusE (aux l) (aux r))]
      [(multS l r)
       (multE (aux l) (aux r))]
      [(newS name args)
       (newE name (map aux args))]
      [(getS obj fd)
       (getE (aux obj) fd)]
      [(sendS obj mtd arg)
       (sendE (aux obj) mtd (aux arg))]
      [(superS mtd arg)
       (ssendE (thisE)
               super-name
               mtd
               (aux arg))])))

; passage d'une classe utilisateur en classe interne
(define (class-s->e [c : (Symbol * ClassS)]) : (Symbol * Class)
  (type-case ClassS (snd c)
    [(classS super-name fds mtds)
     (pair
      (fst c)
      (classE
       fds
       (map (lambda (mtd)
              (pair
               (fst mtd)
               (exp-s->e (snd mtd) super-name)))
            mtds)))]))

; compilation d'une classe utilisateur brute
(define (compile-class
         [raw : (Symbol * ClassS)]
         [compiled : (Listof (Symbol * ClassS))]) : (Listof (Symbol * ClassS))
  (type-case ClassS (snd raw)
    [(classS super-name fd-names mtds)
     (type-case ClassS (find super-name compiled)
       [(classS super-super-name super-fd-names super-mtds)
        (let ([c (classS
                  super-name
                  (merge-fields fd-names super-fd-names)
                  (merge-methods mtds super-mtds))])
          (cons (pair (fst raw) c)
                compiled))])]))

; fusion des champs
(define (merge-fields
         [fd-names : (Listof Symbol)]
         [super-fd-names : (Listof Symbol)]) : (Listof Symbol)
  (append super-fd-names fd-names))

; fusion des méthodes
(define (merge-methods
         [mtds : (Listof (Symbol * ExpS))]
         [super-mtds : (Listof (Symbol * ExpS))]) : (Listof (Symbol * ExpS))
  (let* ([defined (map fst mtds)]
         [super-defined (map fst super-mtds)]
         [not-redefined (filter (lambda (mtd-name)
                                  (not (member mtd-name defined)))
                                super-defined)]
         [inherited-mtds (map (lambda (mtd-name)
                                (pair
                                 mtd-name
                                 (superS mtd-name (argS))))
                              not-redefined)])
    (append mtds inherited-mtds)))

; tri topologique
(define (topological-sort
         [from : (Symbol * ClassS)]
         [classes : (Listof (Symbol * ClassS))]) : (Listof (Symbol * ClassS))
  (let* ([children (filter (lambda (c)
                             (equal?
                              (classS-super-name (snd c))
                              (fst from)))
                           classes)]
         [children-lists
          (map (lambda (child)
                 (topological-sort child classes))
               children)])
    (cons from (foldl append empty children-lists))))

; compilation des classes utilisateur brutes
(define (compile-classes
         [raws : (Listof (Symbol * ClassS))]) : (Listof (Symbol * Class))
  (let* ([sorted (topological-sort
                  (pair 'Object (classS 'Object empty empty))
                  raws)]
         [compiled (foldl
                    compile-class
                    (list (first sorted)) ; Object pré-compilé
                    (rest sorted))])
    (map class-s->e compiled)))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [expr : Exp]
                [classes : (Listof (Symbol * Class))]
                [this-v : Value]
                [arg-v : Value]) : Value
  (let ([interp-r (lambda (expr)
                    (interp expr classes this-v arg-v))])
    (type-case Exp expr
      [(thisE) this-v]
      [(argE) arg-v]
      [(numE n) (numV n)]
      [(plusE l r)
       (num+ (interp-r l) (interp-r r))]
      [(multE l r)
       (num* (interp-r l) (interp-r r))]
      [(newE class-name args)
       (let ([class (find class-name classes)])
         (if (= (length args)
                (length (classE-field-names class)))
             (objV class-name (map interp-r args))
             (error 'interp "wrong fields count")))]
      [(getE obj fd)
       (type-case Value (interp-r obj)
         [(objV class-name fd-vals)
          (let ([class (find class-name classes)])
            (find fd (map2 pair
                           (classE-field-names class)
                           fd-vals)))]
         [else (error 'interp "not an object")])]
      [(sendE obj mtd arg)
       (let ([obj-v (interp-r obj)])
         (type-case Value obj-v
           [(objV class-name fd-vals)
            (call-method class-name mtd classes obj-v (interp-r arg))]
           [else (error 'interp "not an object")]))]
      [(ssendE obj class-name mtd arg)
       (call-method class-name mtd classes (interp-r obj) (interp-r arg))])))

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

; Recherche dans des listes d'association
(define (find [name : Symbol]
              [pairs : (Listof (Symbol * 'a))]) : 'a
  (cond
    [(empty? pairs)
     (error 'find "not found")]
    [(equal? name (fst (first pairs)))
     (snd (first pairs))]
    [else (find name (rest pairs))]))

; Recherche dans des listes d'association
(define (find-opt [name : Symbol]
                  [pairs : (Listof (Symbol * 'a))]) : (Optionof 'a)
  (cond
    [(empty? pairs) (none)]
    [(equal? name (fst (first pairs)))
     (some (snd (first pairs)))]
    [else (find-opt name (rest pairs))]))

; Appel de méthode
(define (call-method [class-name : Symbol]
                     [method-name : Symbol]
                     [classes : (Listof (Symbol * Class))]
                     [this-v : Value]
                     [arg-v : Value]) : Value
  (type-case Class (find class-name classes)
    [(classE field-names methods)
     (interp (find method-name methods) classes this-v arg-v)]))


;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (check-expr [s : S-Exp] [classes : (Listof S-Exp)]) : Type
  (let ([expr (parse s #f)]
        [typed-raw (map parse-class classes)])
    (typecheck expr typed-raw)))

(define (interp-expr [s : S-Exp] [classes : (Listof S-Exp)]) : Value
  (let ([expr (parse s #f)]
        [typed-raw (map parse-class classes)])
    (begin
      (typecheck expr typed-raw)
      (let* ([untyped-raw (map (lambda (class)
                                 (pair (fst class)
                                       (strip-types (snd class))))
                               typed-raw)]
             [compiled-classes (compile-classes untyped-raw)])
        (interp (exp-s->e expr 'Object)
                compiled-classes
                (objV 'Object empty)
                (numV 0))))))

(test/exn (check-expr
           `42
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {send {get this x} dist 0}
                        {send {get this y} dist 0}}]}))
          "expected object")

(test/exn (check-expr
           `42
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {get this z}}]}))
          "not found")

(test/exn (check-expr
           `42
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {send this get-y 0}}]}))
          "not found")

(test/exn (check-expr
           `42
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : Posn
                     {+ {get this x} {get this y}}]}))
          "expected type")

(test (check-expr
       `42
       (list
        `{class Posn extends Object
           {[x : num] [y : num]}
           [dist {[arg : num]} : num
                 {+ {get this x} {get this y}}]}))
      (numT))

(test/exn (check-expr
           `{new Posn 12}
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {get this y}}]}))
          "wrong fields count")

(test/exn (check-expr
           `{new Posn 12 {new Posn 3 4}}
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {get this y}}]}))
          "expected type")

(test (check-expr
       `{send {new Posn 1 2} clone 0}
       (list
        `{class Posn extends Object
           {[x : num] [y : num]}
           [dist {[arg : num]} : num
                 {+ {get this x} {get this y}}]
           [clone {[arg : num]} : Posn
                  {new Posn {get this x} {get this y}}]}))
      (objT 'Posn))

(test (check-expr
       `{new Posn3D 1 2 3}
       (list
        `{class Posn extends Object
           {[x : num] [y : num]}
           [dist {[arg : num]} : num
                 {+ {get this x} {get this y}}]
           [clone {[arg : num]} : Posn
                  {new Posn {get this x} {get this y}}]}
        `{class Posn3D extends Posn
           {[z : num]}
           [dist {[arg : num]} : num
                 {+ {get this z} {super dist arg}}]}))
      (objT 'Posn3D))

(test/exn (check-expr
           `{new Posn3D 1 2 3}
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {get this y}}]
               [clone {[arg : num]} : Posn
                      {new Posn {get this x} {get this y}}]}
            `{class Posn3D extends Posn
               {[z : num]}
               [dist {[arg : num]} : Posn
                     {new Posn 1 2}]}))
          "bad override")

(test/exn (check-expr
           `{new Posn3D 1 2 3}
           (list
            `{class Posn extends Object
               {[x : num] [y : num]}
               [dist {[arg : num]} : num
                     {+ {get this x} {get this y}}]
               [clone {[arg : num]} : Posn
                      {new Posn {get this x} {get this y}}]}
            `{class Posn3D extends Posn
               {[z : num]}
               [dist {[arg : num]} : num
                     {+ {get this z} {super dist arg}}]
               [clone {[arg : num]} : num
                      arg]}))
          "bad override")

(test (check-expr
       `{new Posn3D 1 2 3}
       (list
        `{class Posn extends Object
           {[x : num] [y : num]}
           [dist {[arg : num]} : num
                 {+ {get this x} {get this y}}]
           [clone {[arg : num]} : Posn
                  {new Posn {get this x} {get this y}}]}
        `{class Posn3D extends Posn
           {[z : num]}
           [dist {[arg : num]} : num
                 {+ {get this z} {super dist arg}}]
           [clone {[arg : num]} : Posn
                  {new Posn3D
                       {get this x}
                       {get this y}
                       {get this z}}]}))
      (objT 'Posn3D))

