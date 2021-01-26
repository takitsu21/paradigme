#lang plait

; Décommentez les tests au fur à mesure de votre avancée dans le sujet.
; La syntaxe #;expr permet de commenter l'expression expr (soit l'atome,
; soit de la parenthèse ouvrante à la parenthèse fermante associée).

;;;;; Arbres ;;;;;

(define-type (Arbre 'a)
  [noeud (valeur : 'a) (fils : (Listof (Arbre 'a)))])
      
(define-type (ArbreBinaire 'a)
  [noeud-binaire (valeur : 'a)
                 (fg : (ArbreBinaire 'a))
                 (fd : (ArbreBinaire 'a))]
  [feuille])



(define arbre
  (noeud 'A (list (noeud 'B
                         (list (noeud 'E empty)))
                  (noeud 'C
                         (list (noeud 'F empty)
                               (noeud 'G empty)
                               (noeud 'H empty)))
                  (noeud 'D
                         (list (noeud 'I empty)
                               (noeud 'J
                                      (list (noeud 'K empty))))))))

(define arbre-binaire
  (noeud-binaire
   'A
   (noeud-binaire
    'B
    (noeud-binaire 'E (feuille) (feuille))
    (noeud-binaire
     'C
     (noeud-binaire 'F (feuille) (noeud-binaire 'G (feuille) (noeud-binaire 'H (feuille) (feuille))))
     (noeud-binaire
      'D
      (noeud-binaire 'I (feuille) (noeud-binaire 'J (noeud-binaire 'K (feuille) (feuille)) (feuille)))
      (feuille))))
   (feuille)))

(define (arbre-map [f : ('a -> 'b)]
                   [arbre : (Arbre 'a)]) : (Arbre 'b)
  (type-case (Arbre 'a) arbre
    [(noeud v fils) (noeud (f v) (map (lambda (x) (arbre-map f x)) fils))]))

(define (arbre->binaire [arbre : (Arbre 'a)]) : (ArbreBinaire 'a)
  (local [(define (aux arbre freres)
            (type-case (Arbre 'a) arbre
              [(noeud v fils)
               (noeud-binaire v (aux2 fils) (aux2 freres))]))
          (define (aux2 l)
            (if (empty? l)
                (feuille)
                (aux (first l) (rest l))))]
    (aux arbre empty)))


(define (est-singleton? l)
  (and (cons? l) (empty? (rest l))))

(define (binaire->arbre [arbre : (ArbreBinaire 'a)]) : (Arbre 'a)
  (local [(define (aux arbre) : (Listof (Arbre 'a))
            (type-case (ArbreBinaire 'a) arbre
              [(noeud-binaire v fg fd) (cons (noeud v (aux fg)) (aux fd))]
              [(feuille) empty]))]
    (let [(foret (aux arbre))]
      (if (est-singleton? foret)
          (first foret)
          (error 'binaire->arbre "codage invalide")))))
    
#;(test (arbre->binaire arbre) arbre-binaire)
#;(test (binaire->arbre arbre-binaire) arbre)
#;(test/exn (binaire->arbre (noeud-binaire 'A (feuille) (noeud-binaire 'B (feuille) (feuille)))) "binaire->arbre")

(define-type Atome
  [symbole (symb : Symbol)]
  [nombre (n : Number)]
  [chaine (str : String)]
  [booleen (bool : Boolean)])

(define (est-atome? [s : S-Exp])
  (not (s-exp-list? s)))

(define (s-exp->atome [s : S-Exp]) : Atome
  (cond
    [(s-exp-symbol? s) (symbole (s-exp->symbol s))]
    [(s-exp-number? s) (nombre (s-exp->number s))]
    [(s-exp-string? s) (chaine (s-exp->string s))]
    [(s-exp-boolean? s) (booleen (s-exp->boolean s))]
    [else (error 's-exp->atome "pas un atome")]))

(define (s-exp->arbre [s : S-Exp]) : (Arbre (Optionof Atome))
  (if (est-atome? s)
      (noeud  (some (s-exp->atome s)) empty)
      (let ([sl (s-exp->list s)])
        (if (est-atome? (first sl))
            (noeud (some (s-exp->atome (first sl)))
                   (map s-exp->arbre (rest sl)))
            (noeud (none)
                   (map s-exp->arbre sl))))))
    
#;(test (s-exp->arbre `(A (B E) (C F G H) (D I (J K))))
      (arbre-map (lambda (x) (some (symbole x))) arbre))
#;(test (s-exp->arbre `((A)))
      (noeud (none) (list (noeud (some (symbole 'A)) empty))))

;;;;; Code Morse ;;;;;

(define-type Impulsion
  [courte]
  [longue]
  [pause])

(define dict
  (list
   (pair #\A (list (courte) (longue)))
   (pair #\B (list (longue) (courte) (courte) (courte))) 
   (pair #\C (list (longue) (courte) (longue) (courte)))
   (pair #\D (list (longue) (courte) (courte)))
   (pair #\E (list (courte)))
   (pair #\F (list (courte) (courte) (longue) (courte)))
   (pair #\G (list (longue) (longue) (courte)))
   (pair #\H (list (courte) (courte) (courte) (courte)))
   (pair #\I (list (courte) (courte)))
   (pair #\J (list (courte) (longue) (longue) (longue)))
   (pair #\K (list (longue) (courte) (longue)))
   (pair #\L (list (courte) (longue) (courte) (courte)))
   (pair #\M (list (longue) (longue)))
   (pair #\N (list (longue) (courte)))
   (pair #\O (list (longue) (longue) (longue)))
   (pair #\P (list (courte) (longue) (longue) (courte)))
   (pair #\Q (list (longue) (longue) (courte) (longue)))
   (pair #\R (list (courte) (longue) (courte)))
   (pair #\S (list (courte) (courte) (courte)))
   (pair #\T (list (longue)))
   (pair #\U (list (courte) (courte) (longue)))
   (pair #\V (list (courte) (courte) (courte) (longue)))
   (pair #\W (list (courte) (longue) (longue)))
   (pair #\X (list (longue) (courte) (courte) (longue)))
   (pair #\Y (list (longue) (courte) (longue) (longue)))
   (pair #\Z (list (longue) (longue) (courte) (courte)))
   (pair #\  (list (pause)))))

#;(test (code "CODE MORSE") "-.-. --- -.. .   -- --- .-. ... .")

#;(test (decode "-.-. --- -.. .   -- --- .-. ... .") "CODE MORSE")



  






