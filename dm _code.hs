-- Fait par:
-- Faical Sid Ahmed Rahmani - 22010400
-- Brice Le Meur - 21810250



-- Représentation des formules

type Var = Char

data Litteral = Pos Var | Neg Var
      deriving (Show, Eq)

type Clause = [Litteral]

type Formule = [Clause]

type Distribution = [(Var, Bool)]

f1 = [[Pos 'a', Pos 'b'], [Neg 'a', Neg 'b'], [Pos 'a', Neg 'b']]
f2 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Neg 'a', Neg 'b']]
f3 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'],[Neg 'a', Pos 'b'], [Neg 'a', Neg 'b']]
f4 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c', Pos 'b'], [Neg 'a', Pos 'b', Neg 'c'],[Neg 'a', Neg 'b']]
f5 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'], [Neg 'a', Pos 'b'], [Neg 'a', Neg 'b']]
f6 = [[Pos 'a', Neg 'a'], [Pos 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Pos 'a', Neg 'b'],[Pos 'a', Pos 'c'], [Pos 'a', Pos 'b', Neg 'c']]


-- **************************** partie 2 *************************************

elimineTauto :: Formule -> Formule
elimineTauto = filter (not . estTauto)

-- Question 3

-- cette fonction permet de retourner la négation du Litteral (ex :negation (Pos 'c') => Neg 'c')
negation :: Litteral -> Litteral
negation (Pos x) = (Neg x)
negation (Neg x) = (Pos x) 

-- Question 4

-- cette fonction permet de déterminer si une clause est tautologie ou non
-- pour chaque Litteral on vérifie si sa négation existe dans la clause ( existe = tautologie -> true )
estTauto :: Clause -> Bool
estTauto [] = False
estTauto (l:ls) 
    |elem (negation l) ls = True
    |otherwise = estTauto ls

--  ******************************** partie 3 ********************************


-- 3.1 Conditions d’arrêt

-- Question 2 

-- cette fonction permet de déterminer si une clause est unitaire ou pas
-- si la clause contient un seul Litteral alors elle est unitaire  
estUnitaire :: Clause -> Bool
estUnitaire c
    |length c == 1 = True
    |otherwise = False

-- Question 3 

-- cette fonction permet de déterminer si une formules est contradictoire
-- pour chaque clause unitaire on verifie s'il existe une clause unitaire qui contient la négation du Litteral (si oui on sort et on retourne true)
estEvidtContradic :: Formule -> Bool
estEvidtContradic [] = False
estEvidtContradic (c:cs)
    |estUnitaire c = if elem [negation (head c)] cs then True else estEvidtContradic cs
    |otherwise = estEvidtContradic cs

-- 3.2 Simplification : règle du littéral seul

-- Question 2

-- cette fonction permet de verifier s'il existe un Litteral seul dans une formule
-- si on a une clause unitaire alors il existe un Litteral seul (retourner true)
existeSeul :: Formule -> Bool
existeSeul [] = False
existeSeul (c:cs)
    |estUnitaire c = True
    |otherwise = existeSeul cs

-- cette fonction permet de retourner le premier Litteral seul dans une formule
-- on suppose que existeSeul renvoie True sur la formule passée à trouveSeul
-- on parcourt les clauses et on verifie si une clause est unitaire on retourne le Litteral seul de cette clause et on sort 
trouveSeul :: Formule -> Litteral
trouveSeul (c:cs)
    |estUnitaire c = head c
    |otherwise = trouveSeul cs
-- Question 3

-- cette fonction permet d'appliquer la règle de simplification (Litteral seul) une fois et une seule.
elimineSeul :: Formule -> Litteral -> Formule
elimineSeul [] l = []
elimineSeul (c:cs) l
    |elem l c = elimineSeul cs l -- si le Litteral seul existe dans la clause on la supprime et on applique la regle sur le reste de la formule
    |elem (negation l) c = [ y | y <- c ,(negation l) /= y] : (elimineSeul cs l) -- si la negation du Litteral existe dans la clause alors on supprime la negation et on applique la regle sur le reste de la formule
    |otherwise = c : elimineSeul cs l -- sinon on laisse la clause et on applique la regle sur le reste de la formule

-- 3.3 Simplification : règle du littéral pur 

-- Question 2

-- cette fonction retourne la liste des litteraux pur d'une formule à l'aide de la fonction aux qui verifie si la negation d'un Litteral n'existe pas dans une formule (N'existe pas -> true)
-- pour chaque clause => pour chaque Litteral , si sa négation n'existe pas dans la formule alors on le garde 
listPur :: Formule -> [Litteral]
listPur f = [  l |  c <- f, l <- c  ,aux f (negation l)]
           where aux [] y = True 
                 aux (x:xs) y = if (elem y x) then False else (aux xs y)

-- cette fonction permet de déterminer si une formule contient un Litteral pur
-- si la liste des Litterals purs de la formule n'est pas vide (il existe au moins un Litteral pur) alors on retourne true sinon false
existePur :: Formule -> Bool
existePur f = length (listPur f) /= 0 

-- cette fonction permet de trouver un Litteral purs et de le retourner
-- on récupere la liste des Litterals purs de la formule et on retourne le premier Litteral pur
trouvePur :: Formule -> Litteral
trouvePur f = head (listPur f)

-- cette fonction permet d'appliquer laa regle de Litteral pur sur une formule
-- pour chaque clause de la formule si elle contient le Litteral pur alors on la supprime et on continue l'application de la regle sur le reste de la formule
eliminePur :: Formule -> Litteral -> Formule
eliminePur [] l = []
eliminePur (c:cs) l 
    |elem l c = eliminePur cs l
    |otherwise = c : eliminePur cs l


-- 3.4 Recherche exhaustive (splitting)

-- Question 2

-- cette fonction permet de déterminer si une formule est satisfaisable en appliquant estSatis sur la formule sans tautologie
dpll :: Formule -> Bool
dpll = estSatis . elimineTauto

-- cette fonction permet de déterminer si une formule est satisfaisable

-- si la formule est vide alors elle est satisfaisable

-- si la formule est contradictoire on retourne false (insatisfaisable)
-- s'il existe un Litteral seul dans la formule alors : on applique la regle du Litteral seul sur la formule et on continue le travail d'une manière récursive
-- s'il existe un Litteral pur dans la formule alors : on applique la regle du Litteral pur sur la formule et on continue le travail d'une manière récursive
-- sinon (otherwise):
-- on applique le splitting avec comme choix le premier Litteral de la formule et si la formule resultat f1 est satisfaisable on retourne true
-- et si f1 n'est pas satisfaisable on applique le splitting sur la négation du premier Litteral de la formule et on verifie si la formule resultat f2 
-- est satisfaisable ou non.
-- remarque : pour l'application du splitting on a utilisé la fonction 'elimineSeul' car les mêmes règles s'appliquent
estSatis :: Formule -> Bool

estSatis [] = True 
estSatis f
   | estEvidtContradic f = False 
   | existeSeul f = estSatis (elimineSeul f (trouveSeul f)) 
   | existePur f =  estSatis (eliminePur f (trouvePur f))
   | otherwise = if estSatis (elimineSeul f (head (head f))) then True else estSatis (elimineSeul f (negation (head (head f))))



-- ******************************** Bonus **************************************

-- Question 4

-- cette fonction permet d'associer une valeur de vérité à un Litteral
associe :: Litteral -> (Var, Bool)
associe (Pos c) = (c, True)
associe (Neg c) = (c, False)

-- cette fonction permet de donner une distribution de valeurs de vérité telle que la formule soit vraie en utilisant la fonction calculDistri
-- si la formule n'est pas satisfaisable on retourne une liste vide
dpllBis :: Formule -> Distribution
dpllBis f = if (estSatis f) then (calculDistri f) else []

-- cette fonction permet de donner une distribution de valeurs de vérité telle que la formule soit vraie

-- si la formule est vide on retourne une distribution vide

-- s'il exitse un Litteral seul dans la formule alors on lui associe une valeur de vérité et puis on ajoute le couple à la distribution 
-- et on applique la règle de Litteral seul sur la formule et on continue le travail d'une manière récursive

-- s'il exitse un Litteral pur dans la formule alors on lui associe une valeur de vérité et puis on ajoute le couple à la distribution 
-- et on applique la règle de Litteral pur sur la formule et on continue le travail d'une manière récursive

-- sinon (otherwise):

-- si l'application du splitting sur la formule avec comme choix le premier Litteral donne une formule f1 satisfaisable alors
-- on associe une valeur de vérité au Litteral choisi et puis on ajoute le couple à la distribution 
-- et on applique le splitting sur la formule et on continue le travail d'une manière récursive


-- sinon (l'application du splitting sur la formule avec comme choix le premier Litteral donne une formule f1 n'est pas satisfaisable) alors
-- on associe une valeur de vérité à la negation du Litteral choisi et puis on ajoute le couple à la distribution 
-- et on applique le splitting sur la formule et on continue le travail d'une manière récursive

-- remarque : pour l'application du splitting on a utilisé la fonction 'elimineSeul' car les mêmes règles s'appliquent

calculDistri :: Formule -> Distribution
calculDistri [] = []
calculDistri f
   | existeSeul f = associe (trouveSeul f) : calculDistri (elimineSeul f (trouveSeul f))
   | existePur f = associe (trouvePur f) : calculDistri (eliminePur f (trouvePur f))
   | otherwise = if estSatis (elimineSeul f (head (head f))) then associe (head (head f)) : calculDistri (elimineSeul f (head (head f))) else associe (negation (head (head f))) : calculDistri (elimineSeul f (negation (head (head f))))





   