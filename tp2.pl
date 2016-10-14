% Definiciones de operadores.
:- op(900,xfy, [ + ]).
:- op(800,xfy, [ * ]).

% Implementación de los predicados.

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

primerAccionNoInterna(0, []).
primerAccionNoInterna(tau*P, L) :- primerAccionNoInterna(P, L).
primerAccionNoInterna(P*_, [P]) :- P \= tau.
primerAccionNoInterna(P+Q, L) :-
	primerAccionNoInterna(P, A),
	primerAccionNoInterna(Q, B),
	union(A, B, L).

reduce(A*P, A, P).
reduce(P+_, A, R) :- reduce(P, A, R).
reduce(_+Q, A, R) :- reduce(Q, A, R).

reduceLista(P, [], P).
reduceLista(tau*P, L, Q) :- reduceLista(P, L, Q).
reduceLista(P, [X|Y], Q) :-
	reduce(P, X, Z),
	X \= tau,
	reduceLista(Z, Y, Q).

unique([], []).
unique([X|Y], B) :- member(X, Y), unique(Y, B).
unique([X|Y], B) :-
	not(member(X, Y)),
	unique(Y, Z),
	B = [X | Z].

trazas(P, T) :-
	findall(X, reduceLista(P, X, _), Y),
	unique(Y, T).

isList([]).
isList([_|_]).

residuo([], _, []).
residuo([X|Y], L, Q) :-
	residuo(X, L, H),
	residuo(Y, L, M),
	union(H, M, Q).
residuo(P, L, Q) :-
	not(isList(P)),
	findall(X, reduceLista(P, L, X), R),
	unique(R, Q).

must([], _).
must([X|Y], L) :-
	must(X, L),
	must(Y, L).
must(P, L) :-
	not(isList(P)),
	residuo(P, tau, QS),
	member(Q, QS),
	primerAccionNoInterna(Q, A),
	member(X, A),
	member(X, L).

puedeReemplazarA(P, Q) :-
	trazas(P, T1),
	trazas(Q, T2),
	union(P, Q, T),
	acciones(P, A1),
	acciones(Q, A2),
	union(A1, A2, A),

	residuo(P, T, M1),
	must(M1, A),
	residuo(Q, T, M2),
	must(M2, A).

equivalentes(P, Q) :-
	puedeReemplazarA(P, Q),
	puedeReemplazarA(Q, P).


% Tests (van un par de ejemplos, agreguen los suyos).

test(0) :- not((acciones(0, L), member(_,L))).

test(1) :- reduceLista(0,[],0).

test(2) :- not(puedeReemplazarA(moneda * (te * 0 + cafe * 0), moneda * te * 0 + moneda * cafe * 0)).
test(3) :- puedeReemplazarA(tau*a*0, a*0).

test(4) :- equivalentes(a*b*(c*0+d*0), a*b*(d*tau*0+c*0)).
test(5) :- not(equivalentes(a*b*0, b*a*0)).

tests :- forall(between(0, 5, N), test(N)). %Actualizar la cantidad total de tests para contemplar los que agreguen ustedes.
