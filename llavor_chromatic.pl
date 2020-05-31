
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
tria(CNF, Lit):- member([Lit], CNF),!.
tria([[Lit|_]|_],Lit).
tria([[Lit|_]|_],-Lit).

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...

simplif(_,[],[]).
simplif(Lit,[X|CNF],[Y|F]):-   NL is -Lit, %negat del literal
                                member(NL, X),
                                delete(X, NL, Y), %eliminem element de la llista
                                \+ Y = [],
                                simplif(Lit, CNF, F).

simplif(Lit,[X|CNF],[X|F]):-   \+ member(Lit, X),
                                NL is -Lit,
                                \+ member(NL, X), %si no esta a la clausula l'afegim
                                simplif(Lit, CNF, F).

simplif(Lit,[X|CNF],F):-       member(Lit, X), %simplifiquem si el literal esta a la clausula
                                simplif(Lit, CNF, F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%
% unCert(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ... pots crear i utilitzar els auxiliars comaminimUn i nomesdUn

unCert(L, CNF):- comaminimUn(L, CNF1), nomesdUn(L, CNF2), append(CNF1, CNF2, CNF).

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...
comaminimUn(L,[L]).
%%%%%%%%%%%%%%%%%%%
% nomesdUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% ...

nomesdUn(L, CNF):- llistaNegativa(L,Ns), combinacions(Ns,CNF).

combinacions([],[]):-!.
combinacions([A|AS],Res):- emparellar(A,AS,R1), append(R1,R2,Res), combinacions(AS,R2).

emparellar(_,[],[]):-!.
emparellar(A,[B|BS],[[A,B]|LS]):- dif(A,B), emparellar(A,BS,LS).

llistaNegativa([],[]):-!.
llistaNegativa([A|AS], [X|XS]):- X is -A, llistaNegativa(AS,XS).


% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
llista(X,X,[X]) :- !. %en cas que siguin iguals I i F
llista(X,Y,[X|Xs]) :-%concatenem x a xs
    X =< Y,%X ha de ser mes petit
    Z is X+1,%sumem 1
    llista(Z,Y,Xs).%next

% llistaDeLlistes(N,M,L)
% donats N i M, retorna una llista de N llistes de tamany M amb nombres del 1 al N*M
% -> L sera la llista a retornar
llistaDeLlistes(N,M,L) :- llistaDeLlistesAux(N,M,1,L).
llistaDeLlistesAux(1,M,X,R) :- T is X+M-1, llista(X,T,L),R = [L],!.
llistaDeLlistesAux(N,M,X,L) :- T is X+M-1,llista(X,T,Laux), V1 is N - 1, V2 is X+M, llistaDeLlistesAux(V1,M,V2,Lrec), append([Laux],Lrec,L).


% Filtra els numeros negatius
negative(Number) :-
   Number < 0.

restriccioColorPerNode([],[]):-!.%no idea lmao puto prolog asdifhadiosfh, pero vols que si hi ha una llista si te un terme negatiu el true o que?
restriccioColorPerNode([N|G],CNF):-
   unCert(N,Resultat),
   restriccioColorPerNode(G,NovaCNF),
   append(NovaCNF,Resultat,CNF).

nth(1,[X|_],X).
nth(K, [_|L],X) :- nth(K1, L, X), K is K1 + 1.


%nth(1,[X|_],X).
%nth(K, [_|L],X) :- nth(K1, L, X), K is K1 + 1.

%restriccioColorsFixes(Graf,[R|Inici],[]).%WIP
restriccioColorsFixes(_,[],[]).
restriccioColorsFixes(_,[(N,C)|Inici],CNF):-
   R is N * C,
   restriccioColorsFixes([],Inici,NovaCNF),
   append(NovaCNF,[[R]],CNF).

% Graf
% [
%  (node1)[1(blau),2(verd),3(vermell)]
%  (node2)[4(blau),5(verd),6(vermell)]
%  (node3)[7(blau),8(verd),9(vermell)]
%  (node4)[10(blau),11(verd),12(vermell)]
% ]

restriccioColorsAdjacentsAux([E],[D],CNF):-
   nomesdUn([E,D],CNF).
restriccioColorsAdjacentsAux([E|Ex],[D|Dx],CNF):-
   nomesdUn([E,D],C),
   restriccioColorsAdjacentsAux(Ex,Dx,NovaCNF),
   append(NovaCNF,C,CNF).
   


   


restriccioColorsAdjacents(_,[],[]):-!.
restriccioColorsAdjacents(Graf,[(E,D)|Arestes],CNF):-
   nth(E,Graf,NodeE),
   nth(D,Graf,NodeD),
   restriccioColorsAdjacentsAux(NodeE,NodeD,C),
   restriccioColorsAdjacents(Graf,Arestes,NovaCNF),
   append(C,NovaCNF,CNF).

%restriccioColorsAdjacents(_,_,[]):-!.  %


%noAmenacesColumnes(N,D):-
%   columnes(N,L), llistesAVars(L,N,VARS), noAmenacesAux(VARS,D).


%%%%%%%%%%%%%%%%%%%
% els nodes del graph son nombres consecutius d'1 a N.
% K es el nombre de colors a fer servir.
% Arestes es la llista d'arestes del graph com a parelles de nodes
% Inici es la llista de parelles (node,num_color) que s'han de forçar
% C sera la CNF que codifica graph coloring problem pel graph donat
codifica(N,K,Arestes,Inici,C):-
   llistaDeLlistes(N,K,Graf),
   restriccioColorPerNode(Graf,CNF1),
   restriccioColorsFixes(Graf,Inici,CNF2),
   restriccioColorsAdjacents(Graf,Arestes,CNF3),
   append(CNF1,CNF2,CNF4),
   append(CNF3,CNF4,C).
   

  %crear la llista de llistes de variables pels colors de cada node
  %crear la CNF que fa que cada node tingui un color
  %crear la CNF que força els colors dels nodes segons Inici
  %crear la CNF que fa que dos nodes que es toquen tinguin colors diferents
  %C sera el resultat d'ajuntar les CNF creades

    
                                 
%%%%%%%%%%%%%%%%%%%%
% resolGraf(N,A,K,Inputs)
% Donat el nombre de nodes, el nombre de colors, les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.

mostrarSolucio([],_,_).
mostrarSolucio([V|Model],Nactual,CMAX):-
   T1 is V - 1,
   T2 is T1 mod CMAX,
   Resultat is T2 + 1,
   write('El node '),write(Nactual),write(' sera del color nº'),write(Resultat),nl,
   Seguent is Nactual + 1,
   mostrarSolucio(Model,Seguent,CMAX).

mostrarSolucio2([],_,_).
mostrarSolucio2([V|Model],Nactual,CMAX):-
   T1 is V - 1,
   T2 is T1 mod CMAX,
   Resultat is T2 + 1,
   write('El node '),write(Nactual),write(' sera del color nº'),write(Resultat),nl,
   Seguent is Nactual + 1,
   mostrarSolucio(Model,Seguent,CMAX).


resol(N,K,A, I):-
   codifica(N,K,A,I,CNF),
   write(CNF),
   write('SAT Solving at k = '),write(K), nl,
   sat(CNF,[],RESULTAT),
   exclude(negative,RESULTAT,ResultatMostrar),
   sort(ResultatMostrar,ResultatMostrarOrdenat),
   %caguendiooooos jo estic mirant pero hi ha codi que no entenc que fa, el unCert?codifica una cnf per tal k una i nomes una d les variables sigui certa
   mostrarSolucio(ResultatMostrarOrdenat,1,K).

%%%%%%%%%%%%%%%%%%%%
% chromatic(N,A,Inputs)
% Donat el nombre de nodes,  les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
% Pista, us pot ser util fer una immersio amb el nombre de colors permesos.
chromatic(N,A,Inputs):- \+ chromaticAux(N,A,Inputs,1).

chromaticAux(N,A,Inputs,K):-
   \+ resol(N,K,A,Inputs),
   NK is K + 1,
   chromaticAux(N,A,Inputs,NK).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% com a query podeu cridar:
% ?- graf1(N,A), chromatic(N,A,[]).
% i aixi amb altres grafs que us definiu com els que hi ha a continuacio:
   

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




























