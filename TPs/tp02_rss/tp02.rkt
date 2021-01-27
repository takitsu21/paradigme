; Cours 02 : Fonctions

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [subE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [appE (fun : Symbol) (args : (Listof Exp))])

; Représentation des définitions de fonctions
(define-type FunDef
  [fd (name : Symbol) (par : (Listof Symbol)) (body : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ...} s)
     (let ([sl (s-exp->list s)])
       (local [(define (aux acc l)
                 (if (empty? l)
                     acc
                     (plusE (parse (first l)) (aux acc (rest l)))))]
         (aux (numE 0) (rest sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (subE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{SYMBOL ANY ...} s)
     (let ([sl (s-exp->list s)])
       (appE (s-exp->symbol (first sl)) (map parse (rest sl))))]
    [else (error 'parse "invalid input")]))

(define (reset1) 1)

(define (checker acc tocheck args)
  (if (or (empty? tocheck) (>= 3 acc))
      acc
      (checker (if (equal? #t (member (first tocheck) args))
                   (add1 acc)
                   (reset1))
               (rest tocheck) args)))

(define (parse-fundef [s : S-Exp]) : FunDef
  (if (s-exp-match? `{define {SYMBOL SYMBOL SYMBOL ...} ANY} s)
      (let ([sl (s-exp->list s)])
        (let ([sl2 (s-exp->list (second sl))])
          (if (>= 3 (checker 1 sl2 sl2))
              (error 'parse-fundef "bad syntax")
              (fd (s-exp->symbol (first sl2))
                  (map s-exp->symbol (rest sl2))
                  (parse (third sl))))))
      (error 'parse-fundef "invalid input")))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (subst-all fdp fdb args)
  (if (empty? args)
      fdb
      (subst (first args) (first fdp) (subst-all (rest fdp) fdb (rest args)))))

(define (interp [e : Exp] [fds : (Listof FunDef)]) : Number
  (type-case Exp e
    [(numE n) n]
    [(idE s) (error 'interp "free identifier")]
    [(plusE l r) (+ (interp l fds) (interp r fds))]
    [(subE l r) (- (interp l fds) (interp r fds))]
    [(multE l r) (* (interp l fds) (interp r fds))]
    [(appE f args)
     (let [(fd (get-fundef f fds))]
       (if (not (equal? (length args) (length (fd-par fd))))
           (error 'interp "wrong arity")
           (interp (subst-all (fd-par fd)
                              (fd-body fd)
                              (map numE (map (lambda (x) (interp x fds)) args)))
                   fds)))]))

; Recherche d'une fonction parmi les définitions
(define (get-fundef [s : Symbol] [fds : (Listof FunDef)]) : FunDef
  (cond
    [(empty? fds) (error 'get-fundef "undefined function")]
    [(equal? s (fd-name (first fds))) (first fds)]
    [else (get-fundef s (rest fds))]))

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in
    [(numE n) in]
    [(idE s) (if (equal? for s) what in)]
    [(plusE l r) (plusE (subst what for l) (subst what for r))]
    [(subE l r) (subE (subst what for l) (subst what for r))]
    [(multE l r) (multE (subst what for l) (subst what for r))]
    [(appE f args) (appE f (map (lambda (x) (subst what for x)) args))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp] [fds : (Listof S-Exp)]) : Number
  (interp (parse e) (map parse-fundef fds)))

(test (interp-expr `{double 3}
                   (list `{define {double x} {+ x x}}))
      6)

(test (interp-expr `{quadruple 3}
                   (list `{define {double x} {+ x x}}
                         `{define {quadruple x} {double {double x}}}))
      12)



( test ( interp-expr `{+} empty ) 0)
( test ( interp-expr `{+ 1} empty ) 1)
( test ( interp-expr `{+ 1 2} empty ) 3)
( test ( interp-expr `{+ 1 2 3 4 5} empty ) 15)


( test ( interp-expr `{f 1 2}
                     ( list `{ define {f x y} {+ x y} })) 3)
( test/exn ( interp-expr `0 ( list `{ define {f} 42})) "invalid input")
( test/exn ( interp-expr `{f 1}
                         ( list `{ define {f x y} {+ x y} })) "wrong arity")
(test (interp-expr `{- 1 2} empty ) -1)

( test/exn ( interp-expr `{f 1 2 3}
                     ( list `{ define {f x y y x x y} {+ x y x} })) "bad syntax")