:- use_module(library(avl)).
:- use_module(library(lists)).
:- use_module(library(terms)).
:- use_module(library(ordsets)).
:- use_module('lib/misc.pl', [ format_atom/3, fresh_pred_sym/1,
			       substitute_term/4,substitute_term_avl/4,
			       substitute_term_guard/4,
			       copy_instantiate/4,get_ord_pairs/2,
			       get_pairs/2,
			       negate/2, bb_inc/1,
			       reset_pred_sym/0
			     ]
	     ).

:- use_module('tags.pl', [
			  check_race_freedom/2,
			  tags_independent/2,
			  get_proc/2,
			  is_recv_from/1,
			  parse_send/6,
			  sym_set/1,
			  parse_recv/6
			 ]).

:- dynamic independent/2,    /* independent(p,q): processes p and q are independent.*/
           unfolded/2,       /* unfolded(p, S): p has been unfolded from S */
	   sent_to/1,        /* sent_to(p): sent to p after unfolding */
	   asserted/1.       /* asserted(cons): cons is valid. */
			  


/*==============================================================================
 Language:
================================================================================

Core languange:
---------------
 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 skip                : no-operation.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
  | x=type(t)        :       - of type t.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, s, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 assign(p, x, q, v)  : process p assigns process q's value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 pair(x, y)          : pair of values x and y.
 cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
 | C=case(p, exp, A) : C and default case d.

(Set) constraints:
------------------
 fresh(p)            : p is fresh.
 emp                 : ∅.
 setOf([a,b,...])    : {a,b,...}.
 element(p, S)       : p in S.
 subset(P, Q)        : P ⊆ Q.
 prop_subset(P, Q)   : P ⊂ Q.
 set_minus(P, Q)     : P\{Q}.
 assume(cons)        : assume cons holds.

Terms are expected to be of the form par([ seq([..,]), ...]).
==============================================================================
==============================================================================*/

/*===================================
 TODOs:
   - conditionals: variables vs constants.
   - recv(p, q, type, v) as primitive, derive others
   - same for send.
   - Fix nondet.
   - check rho assignments.
===================================*/

replace_proc_id(Proc1, Proc, Rho, Rho1) :-
	/*
	Transform all constant assignments for process Proc into mappings for process Proc1.
        Also substitutes occurrences in all values.
	*/
	findall(Proc-Var-Val, avl_member(Proc-Var, Rho, Val), L),
	  (   foreach(Proc-Var-Val, L),
	      fromto(Rho, RhoIn, RhoOut, Rho1),
	      param(Proc1)
	  do  (   avl_delete(Proc-Var, RhoIn, _, RhoIn1),
		  substitute_term(Proc1, Proc, Val, Val1),
		  avl_store(Proc1-Var, RhoIn1, Val1, RhoOut)
	      ;   RhoIn=RhoOut
	      )
	  ).


rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) :-
	/*
	       T:    Process term.
	   Gamma:    Environment containing message buffer for each process pair.
	   Delta:    Prefix of rewritten communication.
	     Rho:    Map from variables to constants.
             Psi:    Remainder term given as map from process to list of actions.
	*/
	(
	  cleanup_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)->
	  true
	/*
	while(p, cond, A): remove after one iteration --bit hacky
	*/
	; functor(T, while, 3),
	  T= while(P, Cond, A),
	  check_cond(Cond, P, Rho),
	  rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma2, Delta2, Rho2, Psi),
	  negate(Cond, NegCond),
	  check_cond(NegCond, P, Rho2)->
	  T1=skip,
	  Gamma1=Gamma2,
	  Delta1=Delta2,
	  Rho1=Rho2,
	  Psi1=Psi
	
	/*
	/*****************************************
	recv: receive if there's a pending message.
	*****************************************/
	; parse_recv(T, Rho, P, Q, Type, X),
	  avl_member(Q-P, Gamma, [V-Type|Vs]) ->
	  T1=skip,
	  append(Delta, [assign(P, X, Q, V)], Delta1),
	  (   Vs==[] ->
	      avl_delete(Q-P, Gamma, _, Gamma1)
	  ;   avl_store(Q-P, Gamma, Vs, Gamma1)
	  ),
	  (
	   /****************************************
	  propagate constant from assignment in Q.
	  ****************************************/
	      propagate_const(Q, V, Rho, V1)
	  ;   V1=V
	  ),
	  update_constants(P, X, V1, Rho, Rho1),
	  Psi=Psi1
	/*
	if(P, Cond, A): syntactic sugar for ite(P, Cond, A, skip).
	*/
	; functor(T, if, 3),
	  T=if(P, Cond, A)->
	  T1=ite(P, Cond, A, skip),
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	ite(P, Cond, A, B): reduce to A, if Cond holds and B, if not Cond holds.
	*/
	; functor(T, ite, 4),
	  T = ite(P, Cond, A, B),
	  (   check_cond(Cond, P, Rho) ->
	      T1=A
	  ;   negate(Cond, NegCond),
	      check_cond(NegCond, P, Rho) ->
	      T1=B
	  )->
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	par([A,B,C,...])
	*/
	; functor(T, par, 1) ->
	  arg(1, T, L),
	  list_to_ord_set(L, OL),
	  (   OL==[] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   OL = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   select(A, OL, LR),
	      (   A==skip->
		  T1=par(LR), Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      )
	  /*
	  rewrite ordered pairs of expressions
	  */
	  ;   get_ord_pairs(OL, Pairs),
	      select(TL-TR, Pairs, _),
	      rewrite_step(par(TL, TR), Gamma, Delta, Rho, Psi, T2, Gamma1, Delta1, Rho1, Psi1)->
	      list_to_ord_set([TL,TR], Ts),
	      ord_subtract(OL, Ts, Ts1),
	      unpack_par(T2, T2L),
	      append([T2L,Ts1], L2),
	      T1=par(L2)
	  )
	  /*
	  seq([A|B])
	  */
	; functor(T, seq, 1) ->
	  arg(1, T, L),
	  (   L == [] ->
	      T1=skip, Gamma1=Gamma, Delta1=seq(Delta), Rho1=Rho, Psi=Psi1
	  ;   L = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L=[A|B],
	      (  A==skip ->
		  T1=seq(B),Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1) ->
		  T1=seq([A1|B])
	      )
	  )

	
	/**********************
	        Loops
	**********************/

	/* tick:
	Assumed to contain a single send/recv pair.
	All actions under tick are predicated by the receipt of the respecitve message.
	*/
	; functor(T, par, 2),
	  arg(1, T, Tick),
	  arg(2, T, B),
	  functor(Tick, tick, 2),
	  Tick=tick(P, A),
	  mk_pair(A, B, T0, _),
	  mk_pair(skip, B, T2, _),
	  here(1),
	  rewrite(T0, Gamma, [], Rho, Psi, T2, Gamma, Delta2, Rho1, _)->
	  T1=par(skip, B),
	  Gamma1=Gamma,
	  append(Delta, if(P, nondet, seq(Delta2)), Delta1)
	  
	
	/*===========
	residual-for
	===========*/
        %G0 := G ∪ unfolded(p*)
	%A || B[p*/p],G0,D ~~> skip,G, (D;D1)
	%----------------------
	%[A || for(p/{p*})B] ,G,D ~~> skip,G,(D; atomic(D1))

	; functor(T, par, 2),
	  mk_pair(A, For, T, Switched),
	  functor(For, for, 4),
	  For=for(M,Q,{P},B),
	  assert(unfolded(P, {P})),
	  copy_instantiate(B, Q, P, B1),
	  rewrite(par(A, B1), Gamma, [], Rho, Psi, par(C, skip), Gamma, Delta2, Rho2, _)->
	  mk_pair(C, skip, T1, Switched),
	  Rho1=Rho2,
	  Gamma1=Gamma,
	  append(Delta, [atomic(seq(Delta2))], Delta1) 
	
	/*
	============
	Unfold recv
	===========
	G |- unfolded(p)
	G1 := (G-unfolded(p)) ∪ recvFrom(p)
	-------------------------------
	v <- recv({p}),G, D ~~>
	v <- recv(p),G1,D
	*/
	; parse_recv(T, Rho, P, S, Type, X),
	  unfolded(Proc, S)->
	  T1=recv(P, e_pid(Proc), Type, X),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  retractall(unfolded(Proc, S))

	/*
	===========
	unfold-send
	===========
	*/
	; parse_send(T, Rho, P, Q, Type, V),
	  unfolded(Q, S)->
	  T1=send(P, e_pid(Q), Type, V),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  retractall(unfolded(_, S)),
	  assert(sent_to(Q))

	/*
	================
	for-loop
	================
	p* fresh
	par(A(p*), sym(Q, s*, B)) ~~>
	par(skip, par(sym(P, s*\p1, B), C(p1)))
	---------------------------------------
	par(for(m, P, s, A), sym(Q, s, B)) ~~>
	par(skip, sym(Q, s, C))
	*/
	; functor(T, par, 2),
	  arg(1, T, For),
	  parse_for(For, M, P, S, R, Inv, A),
	  arg(2, T, Sym),
	  Sym=sym(Q, S, B),
	  make_instance(Proc),
	  copy_instantiate(A, P, Proc, A1),
	  copy_instantiate(B, Q, Proc, B1),
	  substitute_term(Proc, P, Rho, Rho2),
	  mk_pair(A1, B1, TA, Switched),
	  mk_pair(skip, C, TC, Switched),
	  assert(unfolded(Proc, S)),
	  rewrite(TA, Gamma, [], Rho2, Psi, TC, Gamma, Delta2, Rho3, _)->
	  substitute_term(P, Proc, Rho3, Rho1),
	  substitute_term(Q, Proc, C, C1),
	  T1=par(skip, sym(Q,S,C1)), 
	  Gamma1=Gamma,
          substitute_term(P, Proc, Delta2, Delta3),
	  append(Delta, [for(M, P, S, R, Inv, seq(Delta3))], Delta1)

	/*
	par(seq([ite(P, Cond, A, B), C]), D): reduce both par(A,C) and par(B, C) to skip.
	*/
	/*TODO: keep assignments in rho that are occur on both branches.*/
	; functor(T, par, 2),
	  T=par(TA, D),
	  (   functor(TA, seq, 1)->
	      TA=seq([ITE|C]),
	      functor(ITE, ite, 4),
	      ITE=ite(P, Cond, A, B)
	  ;   functor(TA, ite, 4) ->
	      TA=ite(P, Cond, A, B),
	      C=[]
	  ),
	  mk_pair(seq([A|C]), D, TA0, SwitchedA),
	  mk_pair(seq([B|C]), D, TB0, SwitchedB),
	  mk_pair(skip, D, TA1, SwitchedA),
	  mk_pair(skip, D, TB1, SwitchedB),
	  rewrite(TA0, Gamma, [], Rho, Psi, TA1, Gamma2, DeltaA, RhoA, _),
	  rewrite(TB0, Gamma, [], Rho, Psi, TB1, Gamma2, DeltaB, RhoB, _)->
          intersect_avl(RhoA, RhoB, Rho1),
	  clean_delta(DeltaA, DeltaA1),
	  clean_delta(DeltaB, DeltaB1),
	  append(Delta, [ite(P, Cond, DeltaA1, DeltaB1)], Delta1),
	  Gamma1=Gamma2,
	  T1=par(skip, D),
	  Psi1=Psi
	
	/************************
	-------------
	Sym-Sym-Remove
	-------------
	
        p*: A || Π(q:Q) B [{p*}/P], G, D0 ~~> skip,G,(D0; D1)
        ----------------------------
        Π(p:P) A || Π(q:Q) B, G,D ~~>skip,G,(D; Π(p:P) D1[p/p*])
	*/
        ; functor(T, par, 2),
	  arg(1, T, SymA),
	  arg(2, T, SymB),
	  functor(SymA, sym, 3),
	  SymA=sym(P, SP, A),
	  functor(SymB, sym, 3),
	  SymB=sym(Q, SQ, B),
	  make_instance(Proc),
	  here(1),
	  copy_instantiate(A, P, Proc, A1),
	  substitute_term({Proc}, SP, B, B1),
	  substitute_term(Proc, P, Rho, Rho2),
	  mk_pair(A1, sym(Q, SQ, B1), TAB, Switched),
	  mk_pair(C, skip, TC, Switched),
	  rewrite(TAB, Gamma, [], Rho2, _, TC, Gamma, Delta2, Rho3, _),
	  smaller_than(C,A1)->
	  substitute_term(P, Proc, C, C1),
	  substitute_term(P, Proc, Rho3, Rho1),
	  T1=par(sym(P,SP,C1), skip),
	  Gamma1=Gamma,
          substitute_term_guard(P, Proc, Delta2, Delta3),
	  substitute_term(SP, {Proc}, Delta3, Delta4),
	  append(Delta, [sym(P, SP, seq(Delta4))], Delta1)
	/* 
	-------------
	For-iter
	-------------
	(A[xp/x] || B),G, assume(I) ~~> skip || B,G,(assume(I);D1)
	-----------------------------------------
	(for(x:X) A) || B,G,D ~~> B,G,D ○ for(x:X) D1 end
	*/
	; functor(T, par, 2),
	  arg(1, T, For),
	  arg(2, T, B),
	  parse_for(For, M, X, Xs, R, Inv, A),
	  make_instance(Index),
	  copy_instantiate(A, X, Index, A1),
	  mk_pair(A1, B, A1B, Switched),
	  mk_pair(skip, B, SkipB, Switched),
	  rewrite(A1B, Gamma, [], Rho, Psi, SkipB, Gamma, Delta2, Rho1, _)->
	  T1=par(skip, B),
	  Gamma1=Gamma,
	  substitute_term(X, Index, Delta2, Delta3),
	  append(Delta, [for(M, X, Xs, R, Inv, seq(Delta3))], Delta1)

	/*
	-------------
	Sym-Loop
	-------------
	p*: A || B [{p*}/P], G, D0 ~~> B, G,(D0; D1)
	----------------------------
	Π(p:P) A || B, G,D ~~> B,G,(D; Π(p:P) D1[p/p*])
	*/
	; functor(T, par, 2),
	  arg(1, T, SymA),
	  arg(2, T, B),
	  functor(SymA, sym, 3),
	  SymA=sym(P, S, A),
	  make_instance(Proc),
	  copy_instantiate(A, P, Proc, A1),
	  substitute_term(Proc, P, Rho, Rho2),
	  substitute_term({Proc}, S, B, B1),
	  mk_pair(A1, B1, A1B1, Switched),
	  mk_pair(skip, B1, SkipB1, Switched),
	  rewrite(A1B1, Gamma, [], Rho2, Psi, SkipB1, Gamma, Delta2, Rho3, _) ->
	  T1=par(skip, B),
	  substitute_term(P, Proc, Rho3, Rho1),
	  Gamma1=Gamma,
          substitute_term(P, Proc, Delta2, Delta3),
          substitute_term(S, {Proc}, Delta3, Delta4),
	  append(Delta, [sym(P, S, seq(Delta4))], Delta1)
	

	/*
	----------
	Sym-Repeat
	----------
	G0 := G ∪ unfolded(p*)
	If G|- unfold_send(p) then P1:={p} and P1:=P o/w.
	p*: A || B[pp/p,{pp}/P], G0, D0 ~~> pp:A,G, (D0;D1)
	-----------------------------------------------------
	Π(p:P) A || for p:P do B, G, D ~~>
	Π(p:P) A ,G, (D; Σp:P1 (D1[p/pp])) 
	*/	
	; functor(T, par, 2),
	  arg(1, T, SymA),
	  arg(2, T, ForB),
	  functor(SymA, sym, 3),
	  SymA=sym(P, S, A),
	  ForB=for(Q, P, S, B),
	  mk_pair(A1, B1, A1B1, Switched),
	  mk_pair(A1, skip, A1Skip, Switched),
	  make_instance(Proc),
	  copy_instantiate(A, P, Proc, A1),
          copy_instantiate(B, P, Proc, B1),
	  substitute_term(Proc, P, Rho, Rho2),
	  assert(unfolded(Proc, S)),
	  rewrite(A1B1, Gamma, [], Rho2, _, A1Skip, Gamma, Delta2, Rho3, _) ->         
	  T1=par(SymA, skip),
          intersect_avl(Rho2, Rho3, Rho1),
	  Gamma1=Gamma,
          substitute_term(P, Proc, Delta2, Delta3),
          (   sent_to(Proc) ->
	      Delta4=[for(Q,P,S,seq(Delta3))]
	  ;   Delta4=[for(Q,_,S,nondet(P, S, seq(Delta3)))]
	  ),
	  append(Delta, Delta4, Delta1)
	
	/*
	Reduce ite
	*/
	; functor(T, ite, 4),
	  T=ite(P, Cond, A, B),
	  rewrite(A, Gamma, [], Rho, _, skip, Gamma, DeltaA, RhoA, _),
	  rewrite(B, Gamma, [], Rho, _, skip, Gamma, DeltaB, RhoB, _)->
	  intersect_avl(RhoA, RhoB, Rho1),
          clean_delta(DeltaA, DeltaA1),
          clean_delta(DeltaB, DeltaB1),
	  append(Delta, [ite(P, Cond, DeltaA1, DeltaB1)], Delta1),
	  T1=skip,
	  Gamma1=Gamma

	/*
	send(p, x, v)
	*/
	; parse_send(T, Rho, P, Q, Type, V),
	  (   avl_fetch(P-Q, Gamma, Vs)
	  ;   Vs=[]
	  ),
	  \+unfolded(Q,_),
%	  substitute_constants(V, P, Rho, V1),
	  append(Vs, [V-Type], Vs1),
	  avl_store(P-Q, Gamma, Vs1, Gamma1),
	  T1=skip,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi=Psi1
        /* grouping of sequential statements:
           group(A,B) := A;B where A;B must be rewritten together.
	*/
        ;  functor(T, group, 2),
           arg(1, T, A),
           arg(2, T, B),
           rewrite(seq([A,B]), Gamma, [], Rho, Psi, skip, Gamma1, Delta2, Rho1, Psi1)->
           T1=skip,
           append(Delta, Delta2, Delta1)

	/*
	par(A, while(P, Cond, B)): continue
	*/
	; functor(T, par, 2),
	  arg(1, T, A),
	  arg(2, T, TB),
	  functor(TB, while, 3),
          TB=while(P, Cond, B),
          check_cond(Cond, P, Rho),
          mk_pair(A, B, Pair, Switched),
          mk_pair(A1, skip, Pair1, Switched),
	  empty_avl(Psi),
          get_proc(A,Q),
          assert(unfolded(Q, {Q})),
	  rewrite(Pair, Gamma, [], Rho, Psi, Pair1, Gamma, Delta2, Rho1, Psi1),
          check_cond(Cond, P, Rho1)->
	  T1=par(A1, TB),
	  append(Delta, [atomic(seq(Delta2))], Delta1),
          Gamma1=Gamma


        /*
	par(A, while(P, Cond, B)): exit
	*/
	; functor(T, par, 2),
	  arg(1, T, A),
	  arg(2, T, TB),
	  functor(TB, while, 3),
          TB=while(P, Cond, B),
          check_cond(Cond, P, Rho),
          mk_pair(A, B, Pair, Switched),
          mk_pair(A1, skip, Pair1, Switched),
	  empty_avl(Psi),
	  rewrite(Pair, Gamma, [], Rho, Psi, Pair1, Gamma, Delta2, Rho1, Psi1),
          negate(Cond, NegCond),
          check_cond(NegCond, P, Rho1)->
	  T1=par(A1, skip),
	  append(Delta, [Delta2], Delta1),
          Gamma1=Gamma

	  /*
	  par(A, B): rewrite ordered pairs.
	  */
	; functor(T, par, 2) ->
	  arg(1, T, A),
	  arg(2, T, B),
          /* rewrite expanded sets */
          (   functor(B, par, 2),
	      B=par(Sym, C),
	      Sym=sym(_, Set, _),
              Set=set_minus(_,_),
	      mk_pair(A, C, Pair, Switched),
	      mk_pair(A1, C1, Pair1, Switched),
	      rewrite_step(Pair, Gamma, Delta, Rho, Psi, Pair1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, par(Sym, C1))
	  ;   functor(A, seq, 1),
	      (   cleanup_seq(A, A1)->
		  T2=par(A1, B),
		  rewrite_step(T2, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)
	      ;   A=seq([C|Cs]),
		  rewrite_step(par(C, B), Gamma, Delta, Rho, Psi, par(C1, B1), Gamma1, Delta1, Rho1, Psi1)->
		  T1=par(seq([C1|Cs]), B1)
	      )
	  ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, B)
	  ;   rewrite_step(B, Gamma, Delta, Rho, Psi, B1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A, B1)
	  )
	).

rewrite(T, Gamma, Delta, Rho, Psi, T2, Gamma2, Delta2, Rho2, Psi2) :-
	(   subsumed_by(T, T2),	    
	    Gamma=Gamma2, Delta=Delta2, Rho=Rho2, Psi=Psi2 
	;   rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)->
	    update_max_delta(T1, Delta1),
	    sanity_check([T1, Gamma1, Delta1, Rho1]),
	    rewrite(T1, Gamma1, Delta1, Rho1, Psi1, T2, Gamma2, Delta2, Rho2, Psi2)
	).	  

greedy_rewrite(T, Gamma, Delta, Rho, Psi, T2, Gamma2, Delta2, Rho2, Psi2) :-
	/* Greedily rewrite term. */
	(   rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)->
	    greedy_rewrite(T1, Gamma1, Delta1, Rho1, Psi1, T2, Gamma2, Delta2, Rho2, Psi2)
	;   T=T2, Gamma=Gamma2, Delta=Delta2, Rho=Rho2, Psi=Psi2 
	).

cleanup_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) :-
	/*
	Remove constructs (such as assign/skip) that do not affect communication.
	*/
	(
	  /*
	  assign(p, x, v): p assigns v to x.
	  */
	  functor(T, assign, 3),
	  T=assign(P, X, V),
	  ground(P) ->
	  T1=skip,
	  append(Delta, [T], Delta1),
	  (   nonvar(V),
	      (   avl_member(P-V, Rho, V1)->
		  avl_store(P-X, Rho, V1, Rho1)
	      ;   avl_store(P-X, Rho, V, Rho1)
	      )
	  ;   throw(assing-to-var(assign(P, X, V)))
	  ),
	  Gamma1=Gamma,
	  Psi1=Psi

	 /* local */
	; local(T) ->
	  T1=skip,
	  append(Delta, [T], Delta1),
	  Gamma1=Gamma,
	  Rho1=Rho
	/*
	Case
	*/
	; functor(T, cases, 4),
	  T=cases(P, X, Cs, _),
	  match_case(P, X, Cs, Rho, Rho1, A) ->
	  T1=A,
	  Gamma1=Gamma, Delta1=Delta,
	  Psi1=Psi
	/*Reduce
	while(p, cond, A): remove while if cond doesn't hold.
	*/
	; functor(T, while, 3),
	  T= while(P, Cond, _),
	  negate(Cond, NegCond),
	  check_cond(NegCond, P, Rho) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  \+contains_var(P,A),
	  rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma, Delta1, Rho1, Psi) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Psi1=Psi
	/*
	sym(P, S, A): reduce A in sym(P, S, A)
	*/
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  empty_avl(Psi),
	  make_instance(Proc),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(A, P, Proc, A1),
				%cleanup_step(A1, Gamma, [], Rho2, Psi, B, Gamma, Delta2, Rho3, Psi) ->
	  greedy_rewrite(A1, Gamma, [], Rho2, Psi, B, Gamma, Delta2, Rho3, _),
	  %rewrite(A1, Gamma, [], Rho2, Psi, B, Gamma, Delta2, Rho3, Psi),
	  smaller_than(B, A1)->
	  substitute_term(P, Proc, B, B1),
	  T1=sym(P, S, B1),
	  replace_proc_id(S, Proc, Rho3, Rho4),
	  substitute_term(P, Proc, Rho4, Rho1),
	  Gamma1=Gamma,
	  (   Delta2 == [] ->
	      Delta1=Delta
	  ;   substitute_term(P, Proc, Delta2, Delta3),
	      append(Delta, [for(_0, P, S, r, true, atomic(seq(Delta3)))], Delta1)
	  ),
	  Psi1=Psi
	/*
	Process remainder term.
	*/
	; functor(T, par, 1),
	  T=par(L),
	  nonvar(Psi),
	  avl_domain(Psi, [P]),
	  \+(talkto(_,_)) ->
	  avl_fetch(P, Psi, Ext),
	  append(L, [seq(Ext)], L1),
	  T1=par(L1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  empty_avl(Psi1)
	/*
	nondet(P, A): instantiate P to a fresh constant.
	*/
	; functor(T, nondet, 2) ->
	  T = nondet(P, A),
	  %fresh_pred_sym(Proc),
	  make_instance(Proc),
	  copy_instantiate(A, P, Proc, T1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/*
	nondet(P, S, A): instantiate P to a fresh constant in set S.
	*/
	; functor(T, nondet, 3) ->
	  T = nondet(P, S, A),
	  %fresh_pred_sym(Proc),
	  make_instance(Proc),
	  assert(asserted(element(Proc, S))),
	  assert(asserted(fresh(Proc))),
	  copy_instantiate(A, P, Proc, T1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/* assume */
	; functor(T, assume, 1) ->
	  arg(1, T, Cons),
	  assert(asserted(Cons)),
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	; functor(T, seq, 1),
	  (   cleanup_seq(T, T1)->
	      Gamma1=Gamma,
	      Delta1=Delta,
	      Rho1=Rho,
	      Psi1=Psi
	  ;   T=seq([A|Rest]),
	      cleanup_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=seq([A1|Rest])
	  )
	; functor(T, par, 1),
	  T=par(L),
	  select(A, L, Rest),
	  cleanup_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	  select(A, L, A1, L1),
	  T1=par(L1)
	).

swap_pid(T, P, Rho, T1, Proc, Rho1) :-
	/*
	Instantiate P to Proc in T, where Proc is a fresh symbol.
	*/
	copy_instantiate(T, P, Proc, T1),
	replace_proc_id(Proc, P, Rho, Rho1).


%instantiate(T, P, Rho, T1, Proc, Rho1) :-
	/*
	Transforms all assignments for P to assignments for proc in Rho.
	*/
	
%	make_instance(Proc),
%	swap_pid(T, P, Rho, T1, Proc, Rho1).

parse_for(For, M, P, S, R, Inv, A) :-	
	(   functor(For, for, 4),
	    For=for(M, P, S, A)-> 
	    Inv=true
	;   functor(For, for, 6),
	    For=for(M, P, S, R, Inv, A) 
	).

clean_delta(Delta, Delta1) :-
	(   Delta==[] ->
	    Delta1=skip
	;   Delta1=seq(Delta)
	).

local(T) :-
	functor(T, Fun, _),
	Locals=[pre, assert, assume],
	memberchk(Fun, Locals).
	
	
update_max_delta(T, Delta) :-
	term_size(Delta, Size),
	max_delta(Max, _, _),
	(   Size>Max->
	    retractall(max_delta(_,_,_)),
	    assert(max_delta(Size, T, Delta))
	;   true
	).

cleanup_seq(T, T1) :-
	/*
	Applies on of the transformations:
	     seq([skip|As]) -->  seq([As]) and
             seq([A])       -->  A
	or fails, otherwise.
	*/
	functor(T, seq, 1),
	(   T=seq([A])->
	    T1=A
	;   T=seq([skip|B]),
	    B\==[]->
	    T1=seq(B)
	).

normalize_seq(T, T1) :-
	/*
	Recursively cleans up a sequential composition.
	*/
	(   nonvar(T),
	    cleanup_seq(T, T2) ->
	    normalize_seq(T2, T1)
	;   T1=T
	).

smaller_than(T, T1) :-
	/* T is either a proper subterm of T1 or skip. */
	(   T==skip
	;   T1\==T,
	    contains_term(T, T1)
	).


subsumed_by(T, T1) :-
/* All behaviour of T is also behaviour of T1. */
	(   T=T1->
	    true
	;   parse_recv(T,  _, P, Q, Type, V),
	    parse_recv(T1, _, P, Q, Type, V)->
	    true
	;   functor(T, par, 1),
	    functor(T1, par, 1),
	    T=par(L),
	    T1=par(L1),
	    permutation(L1, L2),
	    subsumed_by(L, L2)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1)
	    do  subsumed_by(Arg, Arg1)->
		true
	    )
	).

mk_pair(A, B, Pair, Switched) :-
	(   Pair=par(A, B),
	    Switched=false
	;   Pair=par(B, A),
	    Switched=true
	).

mk_pair(A, B, Pair) :-
	mk_pair(A, B, Pair, _).

contains_skip(par(A,B)) :-
	(   A=skip
	;   B=skip
	).

unswitch_pair(par(A, B), Switched, Pair) :-
	(   Switched->
	    Pair=par(B, A)
	;   Pair=par(A, B)
	).

sanity_check(L) :-
	(   foreach(X, L)
	do  nonvar(X)->
	    true
	;   throw(parameter_not_instantiated(X-L))
	).

/* DEBUG: can be erased*/
here(X) :- X=1.
/* END */
match(X, Exp) :-
	(   atomic(X),
	    simple(Exp)
	;   compound(X),
	    compound(Exp)->
	    functor(X, F, Arity),
	    functor(Exp, F, Arity)
	).

update_const_match(P, X, Exp, Rho, Rho1) :-
	(   atomic(X)->
	    avl_store(P-X, Rho, Exp, Rho1)
	;   same_functor(Exp, X),
	    (   foreacharg(ArgX, Exp),
		foreacharg(ArgExp, X),
		fromto(Rho, In, Out, Rho1),
		param(P)
	    do  update_const_match(P, ArgX, ArgExp, In, Out)
	    )
	;   Rho1=Rho
	).

propagate_const(P, X, Rho, X1) :-
	/*
	Substitute all assignments in rho for p's var x.
        If x's value is a composite term, recursively substitute
	assignments for its subterms.
	*/
	(   nonvar(X),
	    /*Process name can't occur as var.*/
	    X\==P, 
	    avl_member(P-X, Rho, X2),
	    \+contains_term(X, X2)->
	    (   simple(X2) ->
		X1=X2
	    ;   compound(X2)->
		(   same_functor(X2, X1),
		    (   foreacharg(Arg, X2),
			foreacharg(Arg1, X1),
			param([P,Rho])
		    do  propagate_const(P, Arg, Rho, Arg1)
		    )
		)
	    )
	;   compound(X) ->
	    (   same_functor(X, X1),
		    (   foreacharg(Arg, X),
			foreacharg(Arg1, X1),
			param([P,Rho])
		    do  propagate_const(P, Arg, Rho, Arg1)
		    )
		)
	;   X1=X
	).

unpack_par(T, L) :-
	/*
	Unpack nested par-expressions into a list.
	*/
	(   functor(T, F, _),
	    F\==par->
	    L=[T]
	;   functor(T, par, 1)->
	    arg(1, T, L)
	;   functor(T, par, 2)->
	    arg(1, T, T1),
	    arg(2, T, T2),
	    unpack_par(T1, L1),
	    unpack_par(T2, L2),
	    append([L1,L2],L)
	).


intersect_avl(A, B, Res) :-
	/*
	Res contains all common assignments between A and B.
        Intersecting with full_avl preserves all constants.
	*/
	(   A==full_avl->
	    Res=B
	;   avl_domain(A, Dom),
	    (   foreach(Key, Dom),
		fromto(empty, In, Out, Res),
		param([A,B])
	    do  (   avl_fetch(Key, A, Val),
		    avl_fetch(Key, B, Val)->
		    avl_store(Key, In, Val, Out)
		;   In=Out
		)
	    )
	).	

update_constants(P, X, V, Rho, Rho1) :-
	(   var(V) ->
	    Rho1=Rho
	;   functor(X, pair, 2),
	    functor(V, pair, 2),
	    X=pair(X1, X2),
	    V=pair(V1, V2) ->
	    update_constants(P, X1, V1, Rho, Rho2),
	    update_constants(P, X2, V2, Rho2, Rho1)
	;   ground(V) ->
	    avl_store(P-X, Rho, V, Rho1)
%	;   throw(pair-matching-error(X,V))
	).

substitute_constants(T, P, Rho, T1) :-
	/*
	In term T substitute all variable bindings defined in Rho to
	produce term T1. Throws exception if variable binding doesn't exist.
	*/
	avl_domain(Rho, Dom),
	(   foreach(Q-Var, Dom),
		fromto(T, In, Out, T1),
		param(Rho, P)
	    do  (  Q==P ->
		    avl_fetch(P-Var, Rho, Val),
		    substitute_term(Val, Var, In, Out)
		;   In=Out
		)
	).

check_cond(Cond, P, Rho) :-
	/*
	Check whether condition Cond holds under
	variable assignment Rho.
	*/
	(   Cond==true ->
	    true
	;   %substitute_constants(Cond, P, Rho, Cond1),
	    propagate_const(P, Cond, Rho, Cond1),
	    catch(Cond1, _, fail)
	).

match_case(P, X, Cases, Rho, Rho1, Res) :-
	/*
	Match variable X of process p with Cases.
        Binds Res to the matching case or fails if no matching case exists.
	Cases=[C_1,C_2,...] with C_i=case(p, exp, A). Throws an exception if
	multiple cases match.
	*/
	propagate_const(P, X, Rho, X1),
	(   foreach(case(P, Exp, A), Cases),
	    fromto(none, In, Out, Res-Exp),
	    param([P, X1])
	do  (   match(X1, Exp)->
		(   In==none->
		    Out=A-Exp
		;   throw(cases-exp-double-match-between(X1,In,Exp))
		)
	    ;   In=Out
	    )
	),
	update_const_match(P, X1, Exp, Rho, Rho1).

is_valid(T) :-
	/*
	If it is in the basic set of axioms or was asserted.
	*/
	(  T=subset(S,S)
	;  T=prop_subset(emp,_)
	;  T=element(P, S),
	   asserted(element(P, S1)),
	   asserted(subset(S1, S))
	;  asserted(T)
	).

check_independent(P, Q) :-
	(   symset(P, S),
	    symset(Q, S1)->
	    tags_independent(S, S1)
	;   symset(P, S)->
	    tags_independent(S, Q)
	;   symset(Q, S)->
	    tags_independent(P, S)
	;   tags_independent(P, Q)
	).

clear_talkto :-
	retractall(talkto(_,_)).

set_talkto(P, Q) :-
	assert(talkto(P,Q)),
	assert(talkto(Q,P)).

init_independent(L) :-
	/*
	L=[(m,n),..] : processes m and n
	are independent.
	*/
	(   foreach((P,Q), L)
	do  assert(independent(P,Q)),
	    assert(independent(Q,P))
	).
generalize(T, T1) :-
%	T=T1.
	replace_inst(T, _, T1).

make_instance(Inst) :-
	fresh_pred_sym(Inst).
				%assert(is_instance(Inst)).

replace_inst(T, X, T1) :-
	(   functor(T, inst, 1)->
	    T1=X
	;   simple(T) ->
	    T1=T
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1),
		param(X)
	    do  replace_inst(Arg, X, Arg1)
	    )
	).

set_not_unfolded(S) :-
	\+(contains_term(set_minus(_,_),S)).

cleanup :-
	clear_talkto,
	retractall(independent(_,_)),
	retractall(talkto(_,_)),
	retractall(unfolded(_,_)),
	retractall(symset(_,_)),
	retractall(sent_to(_)),
	retractall(in_remove),
	retractall(asserted(_)),
	retractall(max_delta(_,_,_)),
	reset_pred_sym.

rewrite(T, Rem, seq(Delta1), Rho1) :-
	assert(max_delta(0, T, [])),
	Delta=[],
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	rewrite(T, Gamma, Delta, Rho, Psi, Rem, Gamma, Delta1, Rho1, Psi).

rewrite_debug(T, Rem, _, _, Delta1, Rho1) :-
	(   rewrite(T, Rem, Delta1, Rho1) ->
	    true
	;   max_delta(_, TMax, DeltaMax),
	    format('Max rewritten term:~n~p~n with prefix:~n~p~n' ,[TMax,DeltaMax]),
	    fail
	).

format_result(Goal, Res) :-
	(   Goal->
	    Res='\e[32mpassed\e[0m'
	;   Res='\e[31mfailed\e[0m'
	).

unit_test :-
%	consult([examples]),
	format('================================================================~n',[]),
	format('~p:~30|~p~t~10+~p~t~13+~p~t~70|~n', ['Name','rewrite','race-check','time']),
	format('================================================================~n',[]),
	findall(T-Rem-Name-Ind, rewrite_query(T, Rem, Ind, Name), L),
	current_output(Out),
	open_null_stream(Null),
	(   foreach(T-Rem-Name-Ind, L),
	    param(Null, Out)
	do (
	     set_output(Null),
	     cleanup,
	     statistics(runtime, [Time0|_]),
	     format_result(catch(check_race_freedom(T, T1), _, fail), Race) ->
	     %findall(P-Q, tags_independent(P, Q), IndSet),
	     format_result(rewrite(T1, Rem, _, _), Rewrite)->
	     statistics(runtime, [Time1|_]),
	     Time is (Time1-Time0),
	     set_output(Out),
%	     format('Independent processes:~p~n',[IndSet]),
	     format('~p:~t~30|~p~t~21+~p~t~18+~t~d~3+~t ms~50|~n', [Name,Rewrite,Race,Time])
	   )
	),
	format('================================================================~n',[]).
