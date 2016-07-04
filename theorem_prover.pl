/* get new clauses */

clausePair(L1, L2, El1, El2) :-
	member(El1, L1),
	member(El2, L2),
	(_, _, Num1, _) = El1,
	(_, _, Num2, _) = El2,
	Num1 < Num2.	

clausePairList(L1, L2, Result):-
  findall((El1, El2), clausePair(L1, L2, El1, El2), Result).	

mapToExList((C1, C2, _, _), (C1, C2)).

isNewClause((Pos, Neg), OrdExList) :-
	\+ ord_memberchk((Pos, Neg), OrdExList),
	!.
	
isNewClause(([[]], [[]]), _).

getNewClause([], _, _, []).

getNewClause([(C1, C2)|T], OrdExList, CurNum, [H|R]) :-
	linkClauses(C1, C2, CurNum, H),
	(HPos, HNeg, _, _) = H,
	isNewClause((HPos, HNeg), OrdExList),
	ord_add_element(OrdExList, (HPos, HNeg), NextOrdExList),
	!,
	NextNum is CurNum + 1,
	getNewClause(T, NextOrdExList, NextNum, R).
	
getNewClause([_|T], OrdExList, CurNum, R) :-
	getNewClause(T, OrdExList, CurNum, R).		

getNewClauses(L1, L2, CurNum, Result) :-
	clausePairList(L1, L2, PairList),
	append(L1, L2, ClauseList),
	maplist(mapToExList, ClauseList, ExList),
	list_to_ord_set(ExList, OrdExList),
	getNewClause(PairList, OrdExList, CurNum, Result).
	
/*find proof*/	

findPreviousClauses([], _, []).
	
findPreviousClauses([H|T], NumList, [H|R]) :-
	(_, _, Num, (Origin1, Origin2)) = H,
	member(Num, NumList),
	!,
	append(NumList, [Origin1, Origin2], NextNumList),
	findPreviousClauses(T, NextNumList, R).
	
findPreviousClauses([_|T], NumList, R) :-
	findPreviousClauses(T, NumList, R).
	
findProof(Result, [], _, Result) :- 
	!,
	false.

findProof(ClauseList, CheckList, _, [EmptyCluase|R]) :-
	member(EmptyCluase, CheckList),
	EmptyCluase = ([[]], [[]], _, (Origin1, Origin2)),
	reverse(ClauseList, RevClauseList),
	findPreviousClauses(RevClauseList, [Origin1, Origin2], R).

findProof(ClauseList, CheckList, CurNum, Result) :-
	getNewClauses(ClauseList, CheckList, CurNum, NextCheckList),
	length(NextCheckList, ListLength),
	NextNum is CurNum + ListLength,
	append(ClauseList, NextCheckList, NextClauseList),
	findProof(NextClauseList, NextCheckList, NextNum, Result).			
  
setNumbers([], _, _, []).  
  
setNumbers([H|T], NumMap, CurNum, [R|S]) :-
	H = (PList, NList, Num, (Origin1, Origin2)),
	member((Origin1, NewOrigin1), NumMap),
	member((Origin2, NewOrigin2), NumMap),	
	R = (PList, NList, CurNum, (NewOrigin1, NewOrigin2)),
	NextNumMap = [(Num, CurNum)|NumMap],
	NextNum is CurNum + 1,
	setNumbers(T, NextNumMap, NextNum, S).   
   
mapToNumMap((_, _, Num, _), (Num, Num)).   
   
removeBadClauses([], []).

removeBadClauses([H|T], [H|S]) :-
	(PList, NList, _, _) = H,
	ord_intersection(PList, NList, []),
	!,
	removeBadClauses(T, S).

removeBadClauses([_|T], S) :-
	removeBadClauses(T, S).
   
createProofList(ClausesLists, Result) :-
	maplist(mapToNumMap, ClausesLists, NumMap),
	length(ClausesLists, ClausesLength),
	CurNum is ClausesLength + 1,
	removeBadClauses(ClausesLists, BaseClauses),
	findProof(BaseClauses, BaseClauses, CurNum, ProofList),
	reverse(ProofList, RevProofList),
	setNumbers(RevProofList, NumMap, CurNum, Result).

addOrigin(Clause, (Clause, axiom)).
   
prove(Clauses, Result) :-
	maplist(addOrigin, Clauses, OriginClauses),
	makeClauseLists(Clauses, 1, ClausesLists),
	createProofList(ClausesLists, ProofList),
	generateClauses(ProofList, ProofClauses),
	append(OriginClauses, ProofClauses, Result).
	
/* make resolution on sorted literals and merge results */

mergeResolution(([], []), ([], []), ([[]], [[]])) :-
	!.
	
mergeResolution((P1, N1), (P2, N2), (P3, N3)) :-
	ord_union(P1, P2, P3),
	ord_union(N1, N2, N3),
	ord_intersection(P3, N3, []).	

firstPosResolution((P1, N1), (P2, N2), R) :-
	ord_intersect(P1, N2, [L|_]),
	ord_selectchk(L, P1, NewP1),
	ord_selectchk(L, N2, NewN2),
	mergeResolution((NewP1, N1), (P2, NewN2), R).
	
makeResolution(L1, L2, R) :-
	firstPosResolution(L1, L2, R).
	
makeResolution(L1, L2, R) :-
	firstPosResolution(L2, L1, R).

linkClauses((P1, N1, C1, _), (P2, N2, C2, _), Num, (P3, N3, Num, (C1, C2))) :-
	makeResolution((P1, N1), (P2, N2), (P3, N3)),
	!.

/*generate clauses from lists*/
      
listToClause([H], H) :-
	!.

listToClause([H|T], v(H, S)) :-
	listToClause(T, S).

generateClause(([[]], _, _, Origin), ([], Origin)) :-
	!.

generateClause((PList, NList, _, Origin), (Clause, Origin)) :-
	maplist(getNegLiteral, NList, NLiterals),
	append(PList, NLiterals, Literals),
	listToClause(Literals, Clause).
	
generateClauses(ClausesList, Result) :-
	maplist(generateClause, ClausesList, Result).
	
/*load clauses into lists*/	
	
isNegLiteral(~(_)).

getNegLiteral(L, ~(L)).
	
getLiteralList(v(L, T), PosList, [P|R]) :-
	isNegLiteral(L),
	!,
	getNegLiteral(P, L),
	getLiteralList(T, PosList, R).
	
getLiteralList(v(L, T), [L|R], NegList) :-
	getLiteralList(T, R, NegList).
	
getLiteralList(L, [], [P]) :-
	isNegLiteral(L),
	!,
	getNegLiteral(P, L).
	
getLiteralList(L, [L], []).
	
makeClauseList(Counter, Clause, Result) :-
	getLiteralList(Clause, PList, NList),
	list_to_ord_set(PList, OrdPList),
	list_to_ord_set(NList, OrdNList),
	Result = (OrdPList, OrdNList, Counter, axiom).
   
makeClauseLists([], _, []).

makeClauseLists([H|T], Counter, [R|S]) :-
	makeClauseList(Counter, H, R),
	NextCounter is Counter + 1,
	makeClauseLists(T, NextCounter, S).	
	
/* twi */

:- op(200, fx, ~).
:- op(500, xfy, v).

main(FileName) :-
    readClauses(FileName, Clauses),
    prove(Clauses, Proof),
    writeProof(Proof).	
		
readClauses(FileName, Clauses) :-
   open(FileName, read, Fd),
   read(Fd, Clauses),
   close(Fd).

writeProof(Proof) :-
   maplist(clause_width, Proof, Sizes),
   max_list(Sizes, ClauseWidth),
   length(Proof, MaxNum),
   write_length(MaxNum, NumWidth, []),
   nl,
   writeClauses(Proof, 1, NumWidth, ClauseWidth),
   nl.

clause_width((Clause, _), Size) :-
   write_length(Clause, Size, []).

writeClauses([], _, _, _).
writeClauses([(Clause,Origin) | Clauses], Num, NumWidth, ClauseWidth) :-
   format('~t~d~*|.  ~|~w~t~*+  (~w)~n',
          [Num, NumWidth, Clause, ClauseWidth, Origin]),
   Num1 is Num + 1,
   writeClauses(Clauses, Num1, NumWidth, ClauseWidth).
