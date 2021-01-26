; Cours 09 : Classes

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des classes
(define-type Class
  [classE (field-names : (Listof Symbol))
          (methods : (Listof (Symbol * Exp)))])

; Représentation des expressions
(define-type Exp
  [thisE]
  [argE]
  [numE (n : Number)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [newE (class : Symbol) (field-values : (Listof Exp))]
  [getE (object : Exp) (field : Symbol)]
  [sendE (object : Exp) (method : Symbol) (arg : Exp)]
  [ssendE (object : Exp) (class : Symbol) (method : Symbol) (arg : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [objV (class-name : Symbol)
        (field-values : (Listof Value))])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

; Analyse d'une classe
(define (parse-class [s : S-Exp]) : (Symbol * Class)
  (cond
    [(s-exp-match? `{class SYMBOL
                      {SYMBOL ...}
                      [SYMBOL ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (let ([mtds (rest (rest (rest sl)))])
         (pair
          (s-exp->symbol (second sl))
          (classE 
           (map s-exp->symbol (s-exp->list (third sl)))
           (map (lambda (mtd)
                  (let ([mtdl (s-exp->list mtd)])
                    (pair (s-exp->symbol (first mtdl))
                          (parse (second mtdl) #t))))
                mtds)))))]
    [else (error 'parse-class "invalid input")]))

; Analyse des expressions
(define (parse [s : S-Exp] [in-method : Boolean]) : Exp
  (local [(define (parse-r s) (parse s in-method))]
    (cond
      [(s-exp-match? `arg s) (if in-method (argE) (error 'parse "invalid input"))]
      [(s-exp-match? `this s) (if in-method (thisE) (error 'parse "invalid input"))]
      [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
      [(s-exp-match? `{+ ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (plusE (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{* ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (multE (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{new SYMBOL ANY ...} s)
       (let ([sl (s-exp->list s)])
         (newE (s-exp->symbol (second sl)) (map parse-r (rest (rest sl)))))]
      [(s-exp-match? `{get ANY SYMBOL} s)
       (let ([sl (s-exp->list s)])
         (getE (parse-r (second sl)) (s-exp->symbol (third sl))))]
      [(s-exp-match? `{send ANY SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (sendE (parse-r (second sl)) (s-exp->symbol (third sl)) (parse-r (fourth sl))))]
      [(s-exp-match? `{ssend ANY SYMBOL SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (ssendE (parse-r (second sl)) (s-exp->symbol (third sl))
                 (s-exp->symbol (fourth sl)) (parse-r (fourth (rest sl)))))]
      [else (error 'parse "invalid input")])))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [classes : (Listof (Symbol * Class))]
                [this-v : Value] [arg-v : Value]) : Value
  (let ([interp-r (lambda (e) (interp e classes this-v arg-v))])
    (type-case Exp e
      [(thisE) this-v]
      [(argE) arg-v]
      [(numE n) (numV n)]
      [(plusE l r) (num+ (interp-r l) (interp-r r))]
      [(multE l r) (num* (interp-r l) (interp-r r))]
      [(newE class-name fd-exprs)
       (let ([c (find class-name classes)])
         (if (= (length fd-exprs) (length (classE-field-names c)))
             (objV class-name (map interp-r fd-exprs))
             (error 'interp "wrong fields count")))]
      [(getE obj fd)
       (type-case Value (interp-r obj)
         [(objV class-name fd-vals)
          (let ([c (find class-name classes)])
            (find fd (map2 pair
                           (classE-field-names c)
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
    [(empty? pairs) (error 'find "not found")]
    [(equal? name (fst (first pairs))) (snd (first pairs))]
    [else (find name (rest pairs))]))

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

(define (interp-expr [expr : S-Exp] [classes : (Listof S-Exp)]) : Value
  (interp (parse expr #f)
          (map parse-class classes)
          (objV 'Object empty)
          (numV 0)))

(define Posn-class
  `{class Posn
     {x y}
     [dist {+ {get this x} {get this y}}]
     [addDist {+ {send this dist 0}
                 {send arg dist 0}}]})

(define Posn3D-class
  `{class Posn3D
     {x y z}
     [dist {+ {get this z} {ssend this Posn dist arg}}]
     [addDist {ssend this Posn addDist arg}]})

(define (interp-posn e)
  (interp-expr e (list Posn-class Posn3D-class)))

(test (interp-posn `{send {new Posn 1 2}
                          dist
                          0})
      (numV 3))

(test (interp-posn `{send {new Posn3D 3 4 5}
                          addDist
                          {new Posn 1 2}})
      (numV 15))
