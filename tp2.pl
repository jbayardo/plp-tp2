% Definiciones de operadores.
:- op(900,xfy, [ + ]).
:- op(800,xfy, [ * ]).

% Implementación de los predicados.

% acciones(+P, -A)
% Estas son literalmente las definiciones del TP
acciones(0, []).
acciones(tau*P, A) :- acciones(P, A).
acciones(P*Q, A) :-
	P \= tau,
	acciones(Q, X),
	union(X, [P], A).
acciones(P+Q, A) :-
	acciones(P, X),
	acciones(Q, Y),
	union(X, Y, A).



% reduce(+P ?A, ?Q)
% Una vez más, literlamente las definiciones del TP
reduce(P*Q, P, Q).
reduce(P+_, A, W) :- reduce(P, A, W).
reduce(_+Q, A, W) :- reduce(Q, A, W).

% reduceLista(+P, ?A, ?Q)
% Un proceso reduce a sí mismo siempre que no ejecutemos nada
reduceLista(P, [], P).
% Nos aseguramos que no nos meta un tau donde no queremos, separando por casos
reduceLista(P, [L|LS], Q) :-
	reduce(P, L, Y),
	L \= tau,
	reduceLista(Y, LS, Q).
reduceLista(P, LS, Q) :-
	reduce(P, tau, Y),
	reduceLista(Y, LS, Q).

% unique(+L, ?B)
unique([], []).
unique([X|Y], B) :- member(X, Y), unique(Y, B).
unique([X|Y], B) :-
	not(member(X, Y)),
	unique(Y, Z),
	B = [X | Z].

% trazas(+P, -T)
trazas(P, T) :-
	% Buscamos todas las X tal que P reduce a algo usando X
	findall(X, reduceLista(P, X, _), Y),
	% Nos aseguramos que la salida sea sin repetidos
	unique(Y, T).

% isList(+L)
isList([]).
isList([_|_]).

% residuo(+X, +L, -Q)
% Manejamos el caso de listas primero, porque es facil de distinguir.
% Simplemente ejecutamos un foldr.
residuo([], _, []).
residuo([X|Y], L, Q) :-
	residuo(X, L, H),
	residuo(Y, L, M),
	union(H, M, Q).
% Si esto no es una lista, buscamos todos los resultados que reducen piola.
residuo(P, L, Q) :-
	not(isList(P)),
	findall(X, reduceLista(P, L, X), R),
	unique(R, Q).

% tausura(+P, ?Q)
% La tausura de un proceso P es la clausura lambda, pero con un nombre cool.
tausura(0, 0).
tausura(tau*P, P).
tausura(P*Q, P*Q) :- P \= tau.
tausura(P + Q, N + M) :- tausura(P, N), tausura(Q, M).

% must(+P, +L)
% La lista vacia vuelve a ser un foldr.
must([], _).
must([X|Y], L) :-
	must(X, L),
	must(Y, L).
must(P, L) :-
	% Para un proceso...
	not(isList(P)),
	% Calculo la clausura lambda (i.e. obtengo el proceso sin taus adelante)
	tausura(P, Q),
	% Obtengo una forma de reducir
	reduce(Q, A, _),
	% Me aseguro que sea miembro de la lista
	member(A, L),
	% Ya fu, no evalues más porque podemos seguir de largo (esto es el existe)
	!.

% sublist(?S, +L)
% Sublistas de una lista
sublist( [], _ ).
sublist( [X|XS], [X|XSS] ) :- sublist( XS, XSS ).
sublist( [X|XS], [_|XSS] ) :- sublist( [X|XS], XSS ).

% puedeReemplazarA(+P, +Q)
puedeReemplazarA(P, Q) :-
	trazas(P, T1),
	trazas(Q, T2),
	union(T1, T2, T),

	acciones(P, A1),
	acciones(Q, A2),
	union(A1, A2, A),

	forall(
		(member(S, T), sublist(L, A)),
		(not((
					residuo(P,S,R1),
					must(R1,L),
					not((residuo(Q,S,R2), must(R2,L))))
			)
		)
	).

resyacc(P, Q, S, L) :-
	trazas(P, T1),
	trazas(Q, T2),
	union(T1, T2, T),

	acciones(P, A1),
	acciones(Q, A2),
	union(A1, A2, A),
	member(S, T), sublist(L, A).

% equivalentes(+P, +Q)
equivalentes(P, Q) :-
	puedeReemplazarA(P, Q),
	puedeReemplazarA(Q, P).


% Tests (van un par de ejemplos, agreguen los suyos).

% differs(+L1,+L2)
% chequea si dos listas no tienen los mismos elementos
differs(T, Q):-
	member(X,T),
	not(member(X, Q)).

sameSet(T, Q):-
	not(differs(T,Q)).

test(0) :- not((acciones(0, L), member(_,L))).

test(1) :- reduceLista(0,[],0).

test(2) :- not(puedeReemplazarA(moneda * (te * 0 + cafe * 0), moneda * te * 0 + moneda * cafe * 0)).
test(3) :- puedeReemplazarA(tau*a*0, a*0).

test(4) :- equivalentes(a*b*(c*0+d*0), a*b*(d*tau*0+c*0)).
test(5) :- not(equivalentes(a*b*0, b*a*0)).

test(6) :- forall(acciones(m*(t*tau*0+c*0), X), X=[t,c,m]).
test(7) :- forall(acciones(0, X), X=[]).

test(8) :- forall(
									reduce(m*(t*0+c*0)+m*j*0+j*c*0+tau*c*0, A, R),
									(
										A = m, R = (t*0+c*0) ;
										A = m, R = (j*0) ;
										A = j, R = (c*0) ;
										A = tau, R = (c*0)
									)
								 ).

test(9) :- forall(reduceLista(0,S,Q), (Q=0, S=[])).
test(10):- forall(
									reduceLista(c * ((a*0) + (b * tau * tau * 0)), S, Q),
									(
										S = [], Q = (c* (a*0+b*tau*tau*0)) ;
										S = [c], Q = (a*0+b*tau*tau*0) ;
										S = [c, a], Q = 0 ;
										S = [c, b], Q = (tau*tau*0) ;
										S = [c, b], Q = (tau*0) ;
										S = [c, b], Q = 0
									)
								 ).

test(11):- forall(trazas(c * ((a*0) + (b * tau * 0)), X),
									(
										X = [[], [c], [c, a], [c, b]]
									)
								 ).
test(12):- forall(trazas((a*0) + (b * 0), X),
									(
										X = [[], [a], [b]]
									)
								 ).

test(13):- forall(residuo((a*0+b*tau*0+b*c*0),[b],Q),
									(
										Q = [tau*0, 0, c*0]
									)
								 ).
test(14):- forall(residuo((a*0+b*tau*0+b*c*0),[c],Q),
									(
										Q = []
									)
								 ).
test(15):- forall(residuo([(a*0+b*tau*0+b*c*0),(b*a*c*0)],[b],Q),
									(
										Q = [tau*0, 0, c*0, a*c*0]
									)
								 ).
test(16):- forall(residuo([(a*0+b*tau*0+b*c*0),(b*a*c*0+b*c*0)],[b],Q),
									(
										Q = [tau*0, 0, a*c*0, c*0]
									)
								 ).

test(17):-  must((a*0+b*0+b*c*0),[a]),
						must((tau*b*0+b*c*0),[b]),
						must((a*0+b*c*0),[a,b]),
						not(must((a*0+b*c*0),[c])),
						not(must([c*0,(b*c*0)],[c])),
						must([b*0,(a*0+b*c*0)],[b]).

tests :- forall(between(0, 17, N), test(N)). %Actualizar la cantidad total de tests para contemplar los que agreguen ustedes.
