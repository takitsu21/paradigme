; Cours 11 : Sous-typage

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
  [recordE (fields : (Listof Symbol)) (args : (Listof Exp))]
  [getE (record : Exp) (field : Symbol)]
  [setE (record : Exp) (field : Symbol) (arg : Exp)])

; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [arrowT (par : Type) (res : Type)]
  [recordT (fields : (Listof Symbol)) (type-fields : (Listof Type))])

; Représentation des liaisons identificateurs type
(define-type TypeBinding
  [tbind (name : Symbol) (type : Type)])

; Environnement pour les types
(define-type-alias TypeEnv (Listof TypeBinding))

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [recordV (ns : (Listof Symbol)) (vs : (Listof Value))])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)


(define (rtf t)
  (recordT-type-fields t))

(define (rf t)
  (recordT-fields t))

(define (arp t)
  (arrowT-par t))

(define (arr t)
  (arrowT-res t))

(define (is-subtype? [t1 : Type ] [t2 : Type ]) : Boolean
  (cond
    [(and (recordT? t1) (recordT? t2))
     (if (< (length (rf t1)) (length (rf t2)))
         #f
         (check-sub-type (rtf t2) (rf t2) (rtf t1) (rf t1)))]
    [(and (arrowT? t1) (arrowT? t2)) (and
                                      (is-subtype? (arp t2) (arp t1))
                                      (is-subtype? (arr t1) (arr t2)))]
     
    [else (equal? t1 t2)]))

(define (check-sub-type t-fds1 fds1 t-fds2 fds2)
  (cond
    [(empty? t-fds1) #t]
    [(and (member (first fds1) fds2)
          (is-subtype? (find (first fds1) fds2 t-fds2) (first t-fds1)))
     (check-sub-type (rest t-fds1) (rest fds1) t-fds2 fds2)]
    [else #f]))

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
    [(s-exp-match? `{record [SYMBOL ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (recordE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) (rest sl))
                (map (lambda (l) (parse (second (s-exp->list l)))) (rest sl))))]
    [(s-exp-match? `{get ANY SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (getE (parse (second sl)) (s-exp->symbol (third sl))))]
    [(s-exp-match? `{set ANY SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (parse (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl))))]
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
    [(s-exp-match? `{[SYMBOL : ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (recordT (map (lambda (p) (s-exp->symbol (first (s-exp->list p)))) sl)
                (map (lambda (p) (parse-type (third (s-exp->list p)))) sl)))]
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
          (if (is-subtype? t2 par-type)
              res-type
              (type-error arg par-type t2))]
         [else (type-error-function fun t1)]))]
    [(recordE fds args) (recordT fds (record-aux fds args env empty))]
    [(getE rec fd) (let ([t1 (typecheck rec env)])
                     (type-case Type t1
                       ((recordT fds t-fds) (find fd fds t-fds))
                       (else (type-error-record rec t1))))]
    [(setE rec fd arg)
     (let ([t1 (typecheck rec env)])
       (type-case Type t1
         ((recordT fds t-fds)
          (let ([t-arg (typecheck arg env)])
            (if (is-subtype? t-arg (find fd fds t-fds))
                t1
                (type-error-record arg t1))))               
         (else (type-error-record arg t1))))]))
                                 
(define (record-aux fds args env mt-types)
  (if (empty? args)
      mt-types
      (let ([t (typecheck (first args) env)])
        (let ([new-env (extend-env (tbind (first fds) t) env)])
          (record-aux (rest fds) (rest args) new-env (cons t mt-types))))))
      
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
(define (type-error-record [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected record "
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
    [(recordE fds args) (recordV fds (map (lambda (exp) (interp exp env)) args))]
    [(getE rec fd)
     (type-case Value (interp rec env)
       [(recordV fds vs) (find fd fds vs)]
       [else (error 'interp "not a record")])]
    [(setE rec fd arg)
     (type-case Value (interp rec env)
       [(recordV fds vs) (recordV fds (update fd (interp arg env) fds vs))]
       [else (error 'interp "not a record")])]))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
    [else (lookup s (rest env))]))

; Recherche dans une liste associative découplée
(define (find [fd : Symbol] [fds : (Listof Symbol)] [vs : (Listof 'a)]) : 'a
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (first vs)]
    [else (find fd (rest fds) (rest vs))]))

; Recherche un symbole dans une liste de symboles
; Renvoie la liste initiale des valeurs avec modification
; de la valeur associée au symbole fd par new-val
(define (update [fd : Symbol] [new-val : Value]
                [fds : (Listof Symbol)] [vs : (Listof Value)]) : (Listof Value)
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (cons new-val (rest vs))]
    [else (cons (first vs) (update fd new-val (rest fds) (rest vs)))]))

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

(test (typecheck-expr `1) (numT))
(test (interp-expr `1) (numV 1))

(test/exn (typecheck-expr `x) "free identifier")
(test (typecheck (parse `x)
                 (extend-env
                  (tbind 'x (numT))
                  mt-env))
      (numT))

(test (typecheck-expr `{+ 1 2}) (numT))
(test (interp-expr `{+ 1 2}) (numV 3))

(test (typecheck-expr `{lambda {[x : num]} x})
      (arrowT (numT) (numT)))

(test (typecheck-expr `{{lambda {[x : num]} x} 1})
      (numT))
(test (interp-expr `{{lambda {[x : num]} x} 1})
      (numV 1))
(test (typecheck-expr `{lambda {[x : (num -> num)]}
                         {lambda {[y : num]}
                           {x {x y}}}})
      (arrowT
       (arrowT (numT) (numT))
       (arrowT (numT) (numT))))
(test (typecheck-expr `{{lambda {[x : (num -> num)]}
                          {lambda {[y : num]}
                            {x {x y}}}}
                        {lambda {[z : num]} {+ z z}}})
      (arrowT (numT) (numT)))
(test (typecheck-expr `{{{lambda {[x : (num -> num)]}
                           {lambda {[y : num]}
                             {x {x y}}}}
                         {lambda {[z : num]} {+ z z}}}
                        1})
      (numT))
(test (interp-expr `{{{lambda {[x : (num -> num)]}
                        {lambda {[y : num]}
                          {x {x y}}}}
                      {lambda {[z : num]} {+ z z}}}
                     1})
      (numV 4))

; Pour les enregistrements
(test (typecheck-expr `{record
                        [x {+ 1 2}]
                        [y {* 3 4}]})
      (recordT
       (list 'x 'y)
       (list (numT)
             (numT))))

(test (typecheck-expr `{get {record
                             [x {+ 1 2}]
                             [y {* 3 4}]} x})
      (numT))

(test (typecheck-expr `{get
                        {get
                         {record
                          [p {record
                              [x {+ 1 2}]
                              [y {* 3 4}]}]}
                         p}
                        x})
      (numT))

(test (typecheck-expr `{set
                        {record
                         [x {+ 1 2}]
                         [y {* 3 4}]}
                        x 0})
      (recordT
       (list 'x 'y)
       (list (numT)
             (numT))))

(test (typecheck-expr `{{lambda {[r : {[x : num] [y : num]}]}
                          {+ {get r x} {get r y}}}
                        {record
                         [x {+ 1 2}]
                         [y {* 3 4}]}})
      (numT))

(test (typecheck-expr `{lambda {[r : {[x : num] [y : num]}]}
                         {+ {get r x} {get r y}}})
      (arrowT
       (recordT
        (list 'x 'y)
        (list (numT)
              (numT)))
       (numT)))

(test (typecheck-expr `{lambda {[r : {[x : num] [y : num]}]}
                         {set r x {get r y}}})
      (arrowT
       (recordT
        (list 'x 'y)
        (list (numT)
              (numT)))
       (recordT
        (list 'x 'y)
        (list (numT)
              (numT)))))

; Pour les enregistrements avec sous-typage
(display "===================================\n")


(test (typecheck-expr `{{lambda {[r : {[x : num]}]}
                          {get r x}}
                        {record
                         [x 1]
                         [y 2]}})
      (numT))

(test (typecheck-expr `{{lambda {[r : {[x : num] [y : num]}]}
                          {get r x}}
                        {record
                         [x 1]
                         [y 2]}})
      (numT))

(test (typecheck-expr `{{lambda {[r : {[p : {[x : num]}]}]}
                          {get {get r p} x}}
                        {record
                         [p {record
                             [x 1]
                             [y 2]}]}})
      (numT))

(test (typecheck-expr `{set {record
                             [p {record
                                 [x 1]}]}
                            p
                            {record
                             [x 1]
                             [y 2]}})
      (recordT
       (list 'p)
       (list (recordT
              (list 'x)
              (list (numT))))))

(test (typecheck-expr `{{lambda {[f : (num -> {[x : num]})]}
                          {get {f 2} x}}
                        {lambda {[n : num]}
                          {record
                           [x n]
                           [y n]}}})
      (numT))

(test (typecheck-expr `{{lambda {[f : ({[x : num] [y : num]} -> num)]}
                          {f {record
                              [x 1]
                              [y 2]}}}
                        {lambda {[r : {[x : num]}]}
                          {get r x}}})
      (numT))

(test (is-subtype? (parse-type `{[y : {[p : num] [t : bool]}]
                                 [x : num]
                                 [z : bool]})
                   (parse-type `{[x : num]
                                 [y : {[t : bool]}]
                                 [z : bool]}))
      #t)

(test (is-subtype? 
       (parse-type `{[w : {[a : bool]}]})
       (parse-type `{[y : {[p : num] [t : bool]}]
                     [x : num]
                     [z : bool]
                     [M : {[l : num] [t : bool] [j : bool]}]})
       )
      #f)
(test (is-subtype? 
       (parse-type `{[w : {[a : bool]}]})
       (parse-type `{[y : {[p : num] [t : bool]}]
                     [x : num]
                     [z : bool]
                     [M : {[l : num] [t : bool] [j : bool]}]})
       )
      #f)

;;; Nb différent d'enregistrement
(display "NB different d'enregistrement\n\n")
(test (is-subtype? (parse-type `{[y : bool] ;t1
                                 [x : num]})
                   (parse-type `{[x : num]})) ;t2
      #t) 
(test (is-subtype? (parse-type `{[y : bool]}) ;t1
                   (parse-type `{[y : bool] ;t2
                                 [x : num]}))
      #f)

;;;; Enregistrement dans le désordre
(display "Enregistrement dans le désordre\n\n")
(test (is-subtype? (parse-type `{[x : num] [y : bool] [z : num]})
                   (parse-type `{[y : bool] [z : num] [x : num]}))
      #t)
(test (is-subtype? (parse-type `{[x : num] [y : bool] [z : num]})
                   (parse-type `{[y : bool] [z : bool] [x : num]}))
      #f)

;;; Enregistrement récursif
(display "Enregistrement récursif\n\n")
(test (is-subtype? (parse-type `{[p : {[x : num] [y : bool]}]})
                   (parse-type `{[p : {[x : num]}]}))
      #t)
(test (is-subtype? (parse-type `{[p : {[x : num]}]})
                   (parse-type `{[p : {[x : num] [y : bool]}]}))
      #f)


;;; Fonctions
(display "Fonctions\n\n")
;Exemple 1 CM
(test (is-subtype? (parse-type `{num -> {[val : num] [gen : num]}})
                   (parse-type `{num -> {[val : num]}}))
      #t)

;Exemple 2 CM
(test (is-subtype? (parse-type `{{[val : num] [gen : num]} -> num})
                   (parse-type `{{[val : num]} -> num}))
      #f)

;Exemple 3 CM
(test (is-subtype? (parse-type `{{[val : num]} -> num}) 
                   (parse-type `{{[val : num] [gen : num]} -> num}))
      #t)
(test/exn (typecheck-expr `{{lambda {[r : {[x : num] [y : num]}]}
                              {+ {get r x} {get r y}}}
                            {record
                             [x {+ 1 2}]}}) "typecheck")
(typecheck-expr `{record [a 0] [b {lambda {[x : num]} x}]})