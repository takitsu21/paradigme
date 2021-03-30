; Cours 09 : Objets

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [thisE]
  [argE]
  [numE (n : Number)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [objE (fields : (Listof (Symbol * Exp)))
        (methods : (Listof (Symbol * Exp)))]
  [getE (object : Exp) (field : Symbol)]
  [sendE (object : Exp) (method : Symbol) (arg : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [objV (fields : (Listof (Symbol * Value)))
        (methods : (Listof (Symbol * Exp)))])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

; Analyse d'une classe
(define (parse [s : S-Exp] [in-method : Boolean]) : Exp
  (local [(define (parse-r s) (parse s in-method))]
    (cond
      [(s-exp-match? `this s) (if in-method (thisE) (error 'parse "invalid input"))]
      [(s-exp-match? `arg s) (if in-method (argE) (error 'parse "invalid input"))]
      [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
      [(s-exp-match? `{+ ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (plusE (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{* ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (multE (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{object {[SYMBOL ANY] ...} [SYMBOL ANY] ...} s)
       (let ([sl (s-exp->list s)])
         (let ([fds (s-exp->list (second sl))]
               [mtds (rest (rest sl))])
           (objE (map (lambda (fd)
                        (let ([fdl (s-exp->list fd)])
                          (pair (s-exp->symbol (first fdl))
                                (parse-r (second fdl)))))
                      fds)
                 (map (lambda (mtd)
                        (let ([mtdl (s-exp->list mtd)])
                          (pair (s-exp->symbol (first mtdl))
                                (parse (second mtdl) #t))))
                      mtds))))]
      [(s-exp-match? `{get ANY SYMBOL} s)
       (let ([sl (s-exp->list s)])
         (getE (parse-r (second sl)) (s-exp->symbol (third sl))))]
      [(s-exp-match? `{send ANY SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (sendE (parse-r (second sl)) (s-exp->symbol (third sl)) (parse-r (fourth sl))))]
      [else (error 'parse "invalid input")])))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [this-v : Value] [arg-v : Value]) : Value
  (type-case Exp e
    [(thisE) this-v]
    [(argE) arg-v]
    [(numE n) (numV n)]
    [(plusE l r) (num+ (interp l this-v arg-v) (interp r this-v arg-v))]
    [(multE l r) (num* (interp l this-v arg-v) (interp r this-v arg-v))]
    [(objE fields methods)
     (objV (map (lambda (fd)
                  (pair (fst fd)
                        (interp (snd fd) this-v arg-v)))
                fields)
           methods)]
    [(getE obj fd)
     (type-case Value (interp obj this-v arg-v)
       [(objV fields methods) (find fd fields)]
       [else (error 'interp "not an object")])]
    [(sendE obj mtd arg)
     (let ([obj-v (interp obj this-v arg-v)])
       (type-case Value obj-v
         [(objV fields methods)
          (interp (find mtd methods)
                  obj-v
                  (interp arg this-v arg-v))]
         [else (error 'interp "not an object")]))]))

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

;;;;;;;;;
; tests ;
;;;;;;;;;

(define (interp-expr [s : S-Exp]) : Value
  (interp (parse s #f)
          (numV 0)
          (numV 0)))

(test (interp-expr `{+ 1 2})
      (numV 3))

(test (interp-expr `{object {}})
      (objV empty empty))

(test (interp-expr `{object
                     {[x {+ 1 2}]}
                     [incr {+ arg 1}]})
      (objV (list (pair 'x (numV 3)))
            (list (pair 'incr (plusE (argE) (numE 1))))))

(test (interp-expr `{get {object
                          {[x {+ 1 2}]}
                          [incr {+ arg 1}]}
                         x})
      (numV 3))

(test (interp-expr `{send {object
                           {[x {+ 1 2}]}
                           [incr {+ arg 1}]}
                          incr 3})
      (numV 4))