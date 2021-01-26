#lang plait

;1.3
(define (somme [L : (Listof Number)]) : Number
  (if (empty? L)
      0
      (+ (first L) (somme (rest L)))))


;1.4

(define (Append [LG : (Listof 'a)]
                [LD : (Listof 'a)]) : (Listof 'a)
  
  (if (empty? LG)
      LD
      (cons (first LG) (Append (rest LG) LD))))

;1.5

;Map
(define (Map [f : ('a -> 'b)]
             [L : (Listof 'a)]) : (Listof 'b)
  (if (empty? L)
      L
      (cons (f (first L)) (Map f (rest L)))))

;Foldr
(define (Foldr [f : ('a 'b -> 'b)]
               [acc : 'b]
               [L : (Listof 'a)]) : 'b
  (if (empty? L)
      acc
      (f (first L) (Foldr f acc (rest L)))))

;Foldl
(define (Foldl [f : ('a 'b -> 'b)]
               [acc : 'b]
               [L : (Listof 'a)]) : 'b
  (if (empty? L)
      acc
      (Foldl f (f (first L) acc) (rest L))))

;2.1

(define-type (Couple 'a 'b)
  [couple (fst : 'a) (snd : 'b)])

;2.2

(define-type (Option 'a)
  [vide]
  [element (valeur : 'a)])

;2.3

( define (find [L : ( Listof ( Couple 'a 'b))]
               [key : 'a]) : ( Option 'b)
   (if ( empty? L)
       ( vide )
       ( type-case ( Couple 'a 'b) ( first L)
          [( couple k v) (if ( equal? k key)
                             ( element v)
                             ( find ( rest L) key))])))

(define couples ( list ( couple 'x 3) ( couple 'y 7)))


(define-type (ArbreBinaire)
  [feuille (f : Number)]
  [noeud (op : (Number Number -> Number))
      (left : ArbreBinaire)
      (right : ArbreBinaire)])

(define (eval [tree : ArbreBinaire]) : Number
  (type-case ArbreBinaire tree
    [(feuille v) v]
    [(noeud op left right) (op (eval left) (eval right))]))
