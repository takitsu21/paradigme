#lang plait #:untyped

(define (find l name)
  (cond
    [(empty? l) (error 'find "not found")]
    [(equal? (fst (first l)) name) (snd (first l))]
    [else (find (rest l) name)]))


(define-syntax-rule (get obj-expr field-id)
  (find (fst obj-expr) 'field-id))

(define-syntax-rule (send obj-expr method-id arg ...)
  (let ([obj obj-expr])
    ((find (snd obj) 'method-id) obj arg ...)))

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
; Les champs sont les mêmes que pour les variantes
; Une seule méthode pour interpréter l'expression dans un environnement

(define-syntax-rule (numC n-ini)
  (pair (list (pair 'n n-ini))
        (list (pair 'interp (lambda (this env)
                              (numV (get this n)))))))

(define-syntax-rule (idC s-ini)
  (pair (list (pair 's s-ini))
        (list (pair 'interp (lambda (this env)
                              (send env lookup (get this s)))))))

(define-syntax-rule (plusC l-ini r-ini)
  (pair (list (pair 'l l-ini)
              (pair 'r r-ini))
        (list (pair 'interp (lambda (this env)
                              (num+ (send (get this l) interp env)
                                    (send (get this r) interp env)))))))

(define-syntax-rule (multC l-ini r-ini)
  (pair (list (pair 'l l-ini)
              (pair 'r r-ini))
        (list (pair 'interp (lambda (this env)
                              (num* (send (get this l) interp env)
                                    (send (get this r) interp env)))))))

(define-syntax-rule (lamC par-ini body-ini)
  (pair (list (pair 'par par-ini)
              (pair 'body body-ini))
        (list (pair 'interp (lambda (this env)
                              (closV (get this par) (get this body) env))))))

(define-syntax-rule (appC fun-ini arg-ini)
  (pair (list (pair 'fun fun-ini)
              (pair 'arg arg-ini))
        (list (pair 'interp (lambda (this env)
                              (send (send (get this fun) interp env)
                                    apply
                                    (send (get this arg) interp env)))))))

; Représentation des valeurs
; Les champs sont les mêmes que pour les variantes
; Une méthode pour extraire l'entier d'un numV
; Une méthode pour appliquer la fonction d'un closV
; Appeler une méthode non supportée par l'objet courant provoque une erreur

(define-syntax-rule (numV n-ini)
  (pair (list (pair 'n n-ini))
        (list (pair 'number (lambda (this)
                              (get this n)))
              (pair 'apply (lambda (this arg)
                             (error 'interp "not a function"))))))

(define-syntax-rule (closV par-ini body-ini env-ini)
  (pair (list (pair 'par par-ini)
              (pair 'body body-ini)
              (pair 'env env-ini))
        (list (pair 'number (lambda (this)
                              (error 'interp "not a number")))
              (pair 'apply (lambda (this arg)
                             (send (get this body)
                                   interp
                                   (extend-env (bind (get this par) arg)
                                               (get this env))))))))

; Représentation des liaisons
; Pas de méthode, les accesseurs suffisent

(define-syntax-rule (bind name-ini val-ini)
  (pair (list (pair 'name name-ini)
              (pair 'val val-ini))
        (list)))

; Manipulation de l'environnement
; Les champs sont les mêmes que pour les variantes
; Une seule méthode pour rechercher la valeur d'un identificateur

(define mt-env
  (pair (list) ; pas de champ pour l'environnement vide
        (list (pair 'lookup (lambda (this s)
                              (error 'lookup "free identifier"))))))

(define-syntax-rule (extend-env b-ini env-ini)
  (pair (list (pair 'b b-ini)
              (pair 'env env-ini))
        (list (pair 'lookup (lambda (this s)
                              (if (equal? s (get (get this b) name))
                                  (get (get this b) val)
                                  (send (get this env) lookup s)))))))

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse s)
  (cond
    [(s-exp-match? `NUMBER s) (numC (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idC (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusC (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multC (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{let {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (appC (lamC (s-exp->symbol (first subst)) (parse (third sl)))
               (parse (second subst)))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamC (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appC (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp e env)
  (send e interp env))

; Fonctions utilitaires pour l'arithmétique
(define (num-op op l r)
  (numV (op (send l number) (send r number))))

(define (num+ l r)
  (num-op + l r))

(define (num* l r)
  (num-op * l r))

;;;;;;;;;
; tests ;
;;;;;;;;;

(define (interp-expr e)
  (interp (parse e) mt-env))

; teste toutes les expressions du langage
(test (send (interp-expr `{let {[x 1]}
                            {{lambda {y} {* {+ x 2} y}}
                             3}})
            number)
      9)
