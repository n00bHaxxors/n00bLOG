
%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretacio I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
   % Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
   tria(CNF,Lit),

   % Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
   simplif(Lit,CNF,CNFS),
   % crida recursiva amb la CNF i la interpretacio actualitzada

   append(I, [Lit], J),
   sat(CNFS, J, M).


%%%%%%%%%%%%%%%%%%
% tria(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
tria(CNF, Lit):- member([Lit], CNF),!. %triem literal de clausual unitaria
tria([[Lit|_]|_],Lit). %en triem un altre qualsevol
tria([[Lit|_]|_],L):- L is -Lit. %provem de triar-lo negat

%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
simplif(_,[],[]).
simplif(Lit,[C|CNF],[C2|F]):-   Negat is -Lit, %eliminem el literal de les clàusules on surti negat, si la clàusula queda buida és que no el podem triar.
                                member(Negat, C),
                                delete(C, Negat, C2),
                                \+ C2 = [],
                                simplif(Lit, CNF, F).

simplif(Lit,[C|CNF],[C|F]):-   \+ member(Lit, C), %simplifiquem en cas que el literal no surti en la clàusula
                                Negat is -Lit,
                                \+ member(Negat, C),
                                simplif(Lit, CNF, F).

simplif(Lit,[C|CNF],F):-       member(Lit, C), %simplifiquem si el literal esta com a clausula unitaria
                                simplif(Lit, CNF, F).

%%%%%%%%%%%%%%%%%%%
% unCert(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
unCert(L, CNF):- comaminimUn(L, CNF1), nomesdUn(L, CNF2), append(CNF1, CNF2, CNF).

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
comaminimUn(L,[L]).

%%%%%%%%%%%%%%%%%%%
% nomesdUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
nomesdUn(L, CNF):- llistaNegativa(L,Ns), combinacions(Ns,CNF).

%%%%%%%%%%%%%%%%%%%
% combinacions(LL,Res)
% Donada una llista de variables, retorna una llista amb totes les combinacions possibles entre elles
combinacions([],[]):-!.
combinacions([A|AS],Res):- emparellar(A,AS,R1), append(R1,R2,Res), combinacions(AS,R2).

%%%%%%%%%%%%%%%%%%%
% emparellar(V,Llista,Sortida)
% Donada una variable i una llista de variables, retorna tots els emparellaments entre V i els valors de la Llista
emparellar(_,[],[]):-!.
emparellar(A,[B|BS],[[A,B]|LS]):- dif(A,B), emparellar(A,BS,LS).

%%%%%%%%%%%%%%%%%%%
% llistaNegativa(LL,Res)
% Nega tots els valors de la llista.
llistaNegativa([],[]):-!.
llistaNegativa([A|AS], [X|XS]):- X is -A, llistaNegativa(AS,XS).

%%%%%%%%%%%%%%%%%%%
% llista(I,F,L)
% Donat un inici i un fi
% Equivalent a un range de python, retorna una llista de valors de I fins a F
llista(X,X,[X]) :- !. %en cas que siguin iguals I i F
llista(X,Y,[X|Xs]) :-%concatenem x a xs
    X =< Y,%X ha de ser mes petit
    Z is X+1,%sumem 1
    llista(Z,Y,Xs).%next

%%%%%%%%%%%%%%%%%%%
% llistaDeLlistes(N,M,L)
% donats N i M, retorna una llista de N llistes de tamany M amb nombres del 1 al N*M
llistaDeLlistes(N,M,L) :- llistaDeLlistesAux(N,M,1,L).
llistaDeLlistesAux(1,M,X,R) :- T is X+M-1, llista(X,T,L),R = [L],!.
llistaDeLlistesAux(N,M,X,L) :- T is X+M-1,llista(X,T,Laux), V1 is N - 1, V2 is X+M, llistaDeLlistesAux(V1,M,V2,Lrec), append([Laux],Lrec,L).

%%%%%%%%%%%%%%%%%%%
% negative(N)
% Filtra els nombres negatius
negative(Number) :-
   Number < 0.

%%%%%%%%%%%%%%%%%%%
% restriccioColorPerNode(LL,CNF) 
% Donat una llista de llistes de variables, retorna una CNF la qual conté la codificació del color únic assignat a cada node del graf.
restriccioColorPerNode([],[]):-!.
restriccioColorPerNode([N|G],CNF):-
   unCert(N,Resultat),
   restriccioColorPerNode(G,NovaCNF),
   append(NovaCNF,Resultat,CNF).

%%%%%%%%%%%%%%%%%%%
% buscarPos(N,M)
% Donat un número N i una llista M, retorna el valor de la posició N de la llista M.
buscarPos(1,[X|_],X).
buscarPos(K, [_|L],X) :- buscarPos(K1, L, X), K is K1 + 1.

%%%%%%%%%%%%%%%%%%%
% restriccioColorsFixes(Graf,[R|Inici],[])
% Donat el graf (llista de llistes de vars) i una llista de colors fixes, retorna una CNF la qual codifica que cada node del graf especificat tingui el color fixe indicat.
restriccioColorsFixes(_,[],_,[]):-!.
restriccioColorsFixes(_,[(N,C)|Inici],CMAX,CNF):-
   R is (N-1) * CMAX + C,
   restriccioColorsFixes([],Inici,CMAX,NovaCNF),
   append(NovaCNF,[[R]],CNF).

%%%%%%%%%%%%%%%%%%%
% restriccioColorsAdjacentsAux(Node1, Node2,CNF)
% Donades dues llistes de variables (2 nodes del graf), codifica la CNF que fa que els 2 nodes no tinguin el mateix color
restriccioColorsAdjacentsAux([E],[D],CNF):-
   nomesdUn([E,D],CNF).
restriccioColorsAdjacentsAux([E|Ex],[D|Dx],CNF):-
   nomesdUn([E,D],C),
   restriccioColorsAdjacentsAux(Ex,Dx,NovaCNF),
   append(NovaCNF,C,CNF).

%%%%%%%%%%%%%%%%%%%
% restriccioColorsAdjacents(Graf,[R|Inici],[])
% Donat el graf (llista de llistes de vars), retorna una CNF que dos nodes connectats per una aresta no continguin el mateix color.
restriccioColorsAdjacents(_,[],[]):-!.
restriccioColorsAdjacents(Graf,[(E,D)|Arestes],CNF):-
   buscarPos(E,Graf,NodeE),
   buscarPos(D,Graf,NodeD),
   restriccioColorsAdjacentsAux(NodeE,NodeD,C),
   restriccioColorsAdjacents(Graf,Arestes,NovaCNF),
   append(C,NovaCNF,CNF).


%%%%%%%%%%%%%%%%%%%
% els nodes del graph son nombres consecutius d'1 a N.
% K es el nombre de colors a fer servir.
% Arestes es la llista d'arestes del graph com a parelles de nodes
% Inici es la llista de parelles (node,num_color) que s'han de forçar
% C sera la CNF que codifica graph coloring problem pel graph donat
codifica(N,K,Arestes,Inici,C):-
   llistaDeLlistes(N,K,Graf),
   restriccioColorPerNode(Graf,CNF1),
   restriccioColorsFixes(Graf,Inici,K,CNF2),
   restriccioColorsAdjacents(Graf,Arestes,CNF3),
   append(CNF1,CNF2,CNF4),
   append(CNF3,CNF4,C).
    
                                 
%%%%%%%%%%%%%%%%%%%%
% mostrarSolucio(Solucio, Color,CMAX)
% Donada una solució, el nombre màxim de colors, i el color pel que anem, mostra per pantalla la pertanyença dels nodes de la solució al color actual i als seguents.
mostrarSolucio(_,Color,CMAX):-
   Color is CMAX + 1,!.
mostrarSolucio(Sol,Color,CMAX):-
   NextColor is Color + 1,
   obtenirNodesColor(Sol,Color,CMAX,L),nl,
   write('color '),write(Color),write(': '),write(L),
   mostrarSolucio(Sol,NextColor,CMAX),!.

%%%%%%%%%%%%%%%%%%%%
% obtenirNodesColor(Sol,Color,CMAX,L)
% Donada una solució al problema, el Color i el nombre màxim de colors, retorna una llista amb els nodes que pertanyen al Color.
obtenirNodesColor([],_,_,[]):-!.
obtenirNodesColor([V|Vl],Color,CMAX,L):-
   T1 is V - 1,
   T2 is T1 mod CMAX, % per obtenir el color
   Color is T2 + 1,
   Node is truncate((T1 / CMAX) + 1),
   obtenirNodesColor(Vl,Color,CMAX,L1),
   append([Node],L1,L),!.
obtenirNodesColor([_|Vl],Color,CMAX,L):-
   obtenirNodesColor(Vl,Color,CMAX,L).

%%%%%%%%%%%%%%%%%%%%
% trobarCromatics(N,K,A,I)
% Resol i mostra el problema de coloritzar un graf, (backtrackejable)
trobarCromatics(N,K,A,I):-
   codifica(N,K,A,I,CNF),
   sat(CNF,[],RESULTAT),
   exclude(negative,RESULTAT,ResultatMostrar),
   sort(ResultatMostrar,ResultatMostrarOrdenat),
   mostrarSolucio(ResultatMostrarOrdenat,1,K).
   
%%%%%%%%%%%%%%%%%%%%
% trobarNombreCromatic(N,K,A,I)
% Retorna el nombre mínim de colors per pintar el graf.
trobarNombreCromatic(N,A,I,K,K):- N >= K, codifica(N,K,A,I,CNF),sat(CNF,[],_),!.
trobarNombreCromatic(N,A,Inputs,K,S):- N >= K, NextK is K + 1, trobarNombreCromatic(N,A,Inputs,NextK,S).


%%%%%%%%%%%%%%%%%%%%
% resol(N,A,Inputs)
% Donat el nombre de nodes,  les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
% Pista, us pot ser util fer una immersio amb el nombre de colors permesos.
resol(N,A,Inputs):- trobarNombreCromatic(N,A,Inputs,1,K),write('El nombre cromàtic és '), write(K),nl,trobarCromatics(N,K,A,Inputs), true.
resol(_,_,_):- write("No s'ha trobat solució cap altre solució, o bé les inicialitzacions contenen dos nodes del mateix color"),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   

% aquest graf te 3 nodes i nombre chromatic 3.
graf0(3,[(1,2),(2,3),(3,1)]).

% aquest graf te 11 nodes i nombre chromatic 4.
graf1(11,[(1,2),(1,4),(1,7),(1,9),(2,3),(2,6),(2,8),(3,5),(3,7),(3,10),
         (4,5),(4,6),(4,10),(5,8),(5,9),(6,11),(7,11),(8,11),(9,11),(10,11)]).

% aquest graf te 23 nodes i nombre chromatic 5.
graf2(23,[(1,2),(1,4),(1,7),(1,9),(1,13),(1,15),(1,18),(1,20),(2,3),(2,6),(2,8),(2,12),(2,14),(2,17),(2,19),
         (3,5),(3,7),(3,10),(3,13),(3,16),(3,18),(3,21),(4,5),(4,6),(4,10),(4,12),(4,16),(4,17),(4,21),
         (5,8),(5,9),(5,14),(5,15),(5,19),(5,20),(6,11),(6,13),(6,15),(6,22),(7,11),(7,12),(7,14),(7,22),
         (8,11),(8,13),(8,16),(8,22),(9,11),(9,12),(9,16),(9,22),(10,11),(10,14),(10,15),(10,22),
         (11,17),(11,18),(11,19),(11,20),(11,21),(12,23),(13,23),(14,23),(15,23),(16,23),(17,23),
         (18,23),(19,23),(20,23),(21,23),(22,23)]).
 
graf3(25,
      [(1,7),(1,5),(1,6),(1,11),(1,16),(1,21),(2,8),(2,14),(2,20),(2,6),(2,3),(2,4),(2,5),(2,7),(2,1),
      (3,9),(3,15),(3,7),(3,2),(3,1),(4,10),(4,8),(4,12),(4,16),(4,5),(4,9),(4,14),(4,19),
      (4,24),(4,3),(4,2),(4,1),(5,9),(5,13),(5,17),(5,21),(5,10),(5,15),(5,1),
      (6,12),(6,18),(6,24),(6,7),(6,8),(6,9),(6,10),(6,11),(6,16),(6,21),(6,2),(6,1),
      (7,13),(7,19),(7,25),(7,11),(7,8),(7,6),(7,3),(7,2),(7,1),(8,14),(8,20),
      (8,12),(8,16),(8,9),(8,7),(8,6),(8,4),(8,3),(8,2),(9,15),(9,13),(9,17),(9,21),
      (9,10),(9,14),(9,19),(9,24),(9,8),(9,7),(9,6),(9,5),(9,4),(9,3),(10,14),(10,18),
      (10,22),(10,15),(10,20),(10,25),(10,9),(10,8),(10,7),(10,6),(10,5),(10,4),
      (11,17),(11,23),(11,12),(11,13),(11,7),(12,16),(12,13),(12,14),(12,15),(12,17),
      (12,22),(12,4),(12,2),(13,19),(13,25),(13,17),(13,21),(13,14),(13,15),(13,18),
      (13,23),(13,12),(13,3),(13,1),(14,20),(14,18),(14,9),(14,8),(14,4),(14,2),(15,19),
      (15,23),(15,20),(15,25),(15,14),(15,13),(15,12),(15,11),(15,10),(15,9),(15,5),
      (15,3),(16,22),(16,17),(16,18),(16,19),(16,20),(16,21),(16,12),(16,11),(16,8),
      (16,6),(17,19),(17,20),(17,22),(17,16),(17,13),(17,12),(17,11),(17,9),(17,7),(17,5),
      (17,2),(18,24),(18,22),(18,19),(18,16),(18,14),(18,13),(18,12),(18,10),(18,8),(18,6),
      (19,24),(19,18),(19,17),(19,16),(19,15),(19,14),(19,13),(19,9),(19,7),(19,4),(19,1),
      (20,24),(20,25),(20,19),(20,18),(20,17),(20,16),(20,15),(20,14),(20,10),(20,8),(20,5),
      (20,2),(21,22),(21,5),(21,1),(22,23),(22,24),(22,25),(22,14),(22,12),(22,10),(22,7),
      (22,2),(23,24),(23,25),(23,22),(23,21),(23,19),(23,18),(23,17),(23,15),(23,13),(23,11),
      (23,8),(23,3),(24,25),(24,23),(24,22),(25,24),(25,23),(25,13)]).




























