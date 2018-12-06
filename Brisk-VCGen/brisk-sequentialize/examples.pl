
/*===========================================
Examples specified as queries of the form

   rewrite_query(T, Rem, Ind, Name).

- T    : Term to be rewritten
- Rem  : Expected remainder term.
- Ind  : List of pairs of independent processes.
- Name : Example name.
===========================================*/

/*==============
 Unfolding:
================*/


/*===========
Unfold-send
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	T=par([
	       seq([
		    assume(element(p, s)),
		    send(m, e_pid(p), v)
		   ]),
	       sym(P, s,
		   recv(P, v)
		  )
	      ]),
	Rem=sym(P, set_minus(s, p), recv(P, v)),
	Name=unfold-send.

/*===========
Unfold-recv
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	T=par([
	       seq([
		    assume(prop_subset(emp, s1)),
		    assume(subset(s1, s)),
		    recv(m, e_pid(s), v)
		   ]),
	       sym(P, s1,
		   send(P, e_pid(m), v)
		  )
	      ]),
	Rem=sym(P, set_minus(s1, Q), send(P, e_pid(m), v)),
	Name=unfold-recv.

/*==============
while-loop-once:
================*/
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	P1=seq([
		recv(m, id),
		send(m, e_var(id), m)
		]),
	P2=while(P, true,
		 seq([
		      send(P, e_pid(m), P),
		      recv(P, v)
		     ])
		),
	T= par([P1, sym(P, s, P2)]),
	Rem=sym(P, s, P2),
	Name=while-sym-once.



/*===========
 For-loop
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(m, e_pid(s), id)]),
	P2=seq([send(P, e_pid(m), P)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=unfold-for-simple.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(m, e_pid(s), id), send(m, e_var(id), m)]),
	P2=seq([send(P,e_pid(m), P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=unfold-for.

/*===========
 sym-while
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	DB=seq([  recv(db, e_pid(s), id),
		  send(db, e_var(id), res)
	       ]),
	Client=seq([
		    send(P, e_pid(db), P),
		    recv(P, v)
		   ]),
	T=(par([sym(P, s, Client),while(db, true, DB)])),
	Name='simple_while_in_proc',
	Rem=while(db, true, DB).

/*==============
Iter-loop:
================*/
rewrite_query(T, Rem, Ind, Name) :-
	P1=seq([
		recv(m, e_pid(s), id),
		send(m, e_var(id), m)
		]),
	P2=while(P, true,
		 seq([
		      send(P, e_pid(m), P),
		      recv(P, e_pid(m), v)
		     ])
		),
	T= par([iter(m, k, P1), sym(P, s, P2)]),
	Rem=sym(P, s, P2),
	Name=iter-while-simple.


/*==============
 Loop free:
================*/

/*===========
"Single ping":
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([send(m,e_pid(p),m), recv(m, x1)]),
	P2=seq([recv(p, id), send(p,e_var(id),p)]),
	T=(par([P1,P2])), Name='single ping'.

/*===========
"Send first":
===========*/

 rewrite_query(T, skip, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(p0,e_pid(p1),p0),recv(p0,x1)]),
	 P2=seq([send(p1, e_pid(p0), p1), recv(p1,x1)]),
	 T=(par([P1,P2])), Name='send first'.

/*===================
"Registry 2proc":
====================*/
/*
--contains a race.
rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	M=seq([send(m,e_pid(p1),r),send(m,e_pid(p2),r),recv(m,x1),send(m,e_pid(r),m)]),
	R=seq([recv(r, x1),recv(r, x2),send(r,e_pid(m),a),recv(r, x3)]),
	P1=seq([recv(p1, x1),send(p1,e_var(x1),p1)]),
	P2=seq([recv(p2, x1),send(p2,e_var(x1),p2)]),
	T= par([M,R,P1,P2]), Name='registry 2-proc'.
*/
/*==============
  For-loops:
==============*/

/*===========
Simple ping
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m, e_pid(Q), m), recv(m, e_pid(Q), x)]),
	P2=seq([recv(P, e_pid(m), id), send(P,e_pid(m),P)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name=simple-ping-loop.

/*===========
Reverse ping
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([recv(m, e_pid(s), id), send(m,e_var(id), m)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=reverse-ping.

/*===========
 Two loops
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m, e_pid(Q), m)]),
	P2=seq([recv(P, id)]),
	T=(par([seq([for(m, Q, s, P1)]), sym(P, s, P2)])),
	Name=two-loops-simple.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([send(m, e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P, e_pid(m), P)]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
	Name=two-loops.

/*============
Two loops var
===============*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P,e_var(id),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name=two-loops-var.

/*===========
 Double ping:
 ===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m),send(m,e_pid(Q),m),recv(m,id1)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x1), recv(P, x2)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name='double ping-false'.

/*================================
Nondet/ Iter-loops / while loops:
==================================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), v)),
	P2=recv(m, v),
	T=(par([P1, P2])),
	Name='nondet'.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), P)),
	P2=seq([recv(m, v)]),
	T=(par([iter(env, k, P1), iter(m, k, P2)])),
	Name='iter-simple'.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, e_pid(q), stop)])),
	T=(par([for(q, _, s, P1), sym(P, s, P2)])),
	Name=work-stealing2.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2)])),
	Name=work-stealing.

/*==================
Multiple processes:
====================*/

/*============
Two-party ping
=============*/

rewrite_query(T, skip, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(m, e_pid(Q), m)]),
	 P2=seq([recv(P, id), send(P,e_pid(n), P)]),
	 P3=seq([recv(n, e_pid(s), x)]),
	 T=(par([for(m, Q, s, P1), sym(P, s, P2), for(m, _, s, P3)])),
	Name='two-party ping'.

/*=========================
Interleaved two-party ping
==========================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(m,n)],
	P1=seq([recv(m, e_pid(s), id), send(m, e_var(id), m)]),
	P2=seq([send(P, e_pid(m), P), send(P, e_pid(n), P), recv(P, e_pid(m), id)]),
	P3=seq([recv(n, e_pid(s), x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2), for(n, _, s, P3)])),
	Name='interleaved two-party ping'.

/*===========================
  Smaller tests geared
  towards specific rules
=============================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	T=(par([send(q, e_pid(p), pair(p, test)), recv(p, pair(id,m))])),
	Name='simple pair'.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	T=(par([send(q, e_pid(p), pair(p, test)), recv(p, e_pid(q), pair(id,m))])),
	Name='simple receive-from'.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(p, ndet, assign(p, act, lookup), assign(p, act, alloc)),
		      send(p, e_pid(sv), pair(act, p))
		     ]),
	Server=seq([recv(sv, pair(act, id))]),
	T=(par([Client, Server])),
	Name='simple ite'.



/*=========================
        Map-reduce
==========================*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([
				send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))
			       ])),
	P3=seq([recv(m, e_pid(s), id)]),
	T=(par([seq([iter(q, k, P1A)]), sym(P, s, P2), iter(m, k, P3)])),
	Rem=sym(P,s, W),
	Name=map-reduce-simple.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))])),
	P3=seq([recv(m, e_pid(s), id)]),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2), iter(m, k, P3)])),
	Name=map-reduce.

/*========
 Conc DB
==========*/


rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(P, ndet, assign(P, act, alloc), assign(P, act, lookup)),
		      send(P, e_pid(db), query, pair(act, P))
		     ]),
	Database=seq([
		      recv(db, e_pid(s), query, pair(act, id))
		     ]),
	T=(par([while(db, true, Database), sym(P, s, Client)])),
	Rem=while(db, true, Database),
	Name='simple-concdb'.



rewrite_query(T, skip, Ind, Name) :-
	P=p,
	Client=seq([
		    recv(P, msg),
		    ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
		   ]),
	Server=ite(db, ndet,seq([
			  send(db, e_pid(p), free),
			  recv(db, e_pid(p), value, _)
				]),
		  send(db, e_pid(p), allocated)
		  ),
	Name=db-ite,
	T=par([Client,Server]).

	
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	P=p,
	Client = seq([
		      assign(P, act, alloc),
		      send(P, e_pid(db), query, pair(act, P)),
		      ite(P, act=alloc,
			  seq([
			       recv(P, msg),
			       ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
			      ]),
			  recv(P, v))
		     ]),
	Database=seq([
		      recv(db, e_pid(p), query, pair(act, id)),
		      ite(  db, act==alloc,
			    ite(db, ndet,
				seq([
				     send(db, e_var(id), free),
				     recv(db, e_var(id), value, _)
			    ]),
				send(db, e_var(id), allocated)
			       ),
			    send(db, e_var(id), val)
			 )
		     ]),
	T=(par([Database,  Client])),
	Rem=skip,
	Name='concdb-seq'.

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(P, ndet, assign(P, act, alloc), assign(P, act, lookup)),
		      send(P, e_pid(db), query, pair(act, P)),
		      ite(P, act==alloc,
			  seq([
			       recv(P, msg),
			       ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
			      ]),
			  recv(P, v))
		     ]),
	Database=seq([
		      recv(db, e_pid(s), query, pair(act, id)),
		      ite(  db, act==alloc,
			    ite(db, ndet,
				seq([
				     send(db, e_var(id), free),
				     recv(db, e_var(id), value, _)
				    ]),
				send(db, e_var(id), allocated)
			       ),
			    send(db, e_var(id), val)
			 )
		     ]),
	T=(par([while(db, true, Database), sym(P, s, Client)])),
	Rem=while(db, true, Database),
	Name='concdb'.


/*====================
tag-server-simplified
======================*/
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Rem=par([Master,TagServer]),
	Name=tagserver-simple,
	T=par([Clients,Master,TagServer]),
	Clients=sym(B, b_Set,
		    seq([
			 send(B, e_pid(a), B), 
			 recv(B, e_pid(a), msg)
			])
		   ),
	Master=while(a, true,
		     seq([
			  recv(a, e_pid(b_Set), id),
			  for(a, P, c_Set,
			      seq([
				   send(a, e_pid(P), a), 
				   recv(a, e_pid(P), msg)
				   ])
			     ),
			  send(a, e_var(id), bla)
			  ])
		    ),
	TagServer=sym(C, c_Set,
		      while(C, true,
			    seq([
				 recv(C, e_pid(a), id),
				 send(C, e_pid(a), bla)
				])
			    )
		      ).
	
/*========
 Firewall
==========*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[(sv, s)],
	Server=seq([
		    recv(sv, pair(id, msg)),
		    ite(sv, msg\==bad, send(sv, e_var(id), msg), skip)
		   ]),
	Firewall=seq([
		      recv(fw, e_pid(s), pair(id, msg)),
		      ite(fw,
			  msg==bad,
			  send(fw, e_var(id), wrong_message),
			  seq([
			       send(fw, e_pid(sv), pair(fw, msg)),
			       recv(fw, e_pid(sv), retmsg),
			       send(fw, e_var(id), retmsg)
			      ])
			 )
		     ]),
	Client=seq([send(P, e_pid(fw), pair(P, m)), recv(P, e_pid(fw), ret)]),
	T=( par([
		 while(sv, true, Server),
		 while(fw, true, Firewall),
		 sym(P, s, Client)
		])
	  ),
	Rem=par([while(sv, true, Server), while(fw, true, Firewall)]),
	Name='firewall'.

/*========
 Registry
 ==========*/

rewrite_query(T, skip, [(m,r)], Name) :-
	Master=seq([
		    for(m, P, s, send(m, e_pid(P), r)),
		    recv(m, e_pid(r), _),
		    send(m, e_pid(r), m)
		   ]),
	Registry=seq([
		      for(r, _, s, recv(r, e_pid(s), id)),
		      send(r, e_pid(m), _),
		      recv(r, e_pid(m), id)
		     ]),
	Procs=sym(P, s, seq([
			     recv(P, id),
			     send(P, e_var(id), P)
			    ])
		 ),
	T=par([Master, Registry, Procs]),
	Name='registry'.


/*===========
 Lock-server
 =============*/
/*
 rewrite_query(T, Res, [], Name) :-

	 Client= seq([
		      send(P, e_pid(sv), lock, P),
		      recv(P, e_pid(sv), ack),
		      iter(P, k,
			   send(P, e_pid(sv), action, pair(act,P))
			  )
		      
		     assign(P, stop, 0),
		     while(P, stop=0,
			   seq([
				send(P, e_pid(sv), lock, P),
				recv(P, e_pid(sv), ack),
				ite(P, ndet,
				    assign(P, act, get),
				    ite(P, ndet,
					assign(P, act, put),
					assign(P, act, unlock)
				       )
				   ),
				send(P, e_pid(sv), action, pair(act,P)),
				ite(P, act==get,
				    recv(P, v),
				    ite(P, act=unlock,
					assign(P, stop, 1),
					skip
				       )
				   )
			       ])
			  )
		    ]),
	 Server=
	 while(sv, true,
	       seq([
		     assign(sv, locked, 0),
		     ite(sv, locked=0,
			 seq([
			      recv(sv, e_pid(s), lock, id),
			      assign(sv, locked, 1),
			      send(sv, e_var(id), ack)
			     ]),
			 skip
			),
		     recv(sv, e_var(id), action, pair(msg,id)),
		     ite(sv, msg==get,
			 send(sv, e_var(id), v),
			 ite(sv, msg=unlock,
			     assign(sv, lock, 0),
			     skip
			    )
			)
		   ])
	      ),
	 T=par([Server,  sym(P, s, Client)]),
	 Res=Server,
	 Name='lock-server'.
*/
/*============
Error handling
===============*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P,e_var(ip),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name=error-simple.

/*================
Cases statements
==================*/

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		recv(A, type(ping), val),
                cases(A, val,
                       [ case(A, ping(Q),
                              seq([
				   send(A, e_pid(Q), pong, A)
				  ])
			     )
                       ],
		      default(A, die(A))
		     )
               ]),
        %%%%% proctype B:
        TB=seq([ send(B, e_pid(A), ping, ping(B)), recv(B, type(pong), var)]),
        %%%%%
        T=par([TA,TB]),
	A=a, B=b,
        Name=cases-minimal.


rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([ recv(A, type(tyCon(ty__Ping)), ds_ddfZ),
                 cases(A, ds_ddfZ,
                       [ case(A, cstr__Ping(Q),
                              send(A, e_pid(Q), tyCon(ty__ProcessId), A)
			     )
			     ],		     
                       _)
               ]),
        %%%%% proctype B:
        TB=seq([ assign(B, anf0, cstr__Ping(B)),
                 send(B, e_pid(A), tyCon(ty__Ping), anf0),
                 recv(B, type(tyCon(ty__ProcessId)), q)
               ]),
        %%%%%
	A=a, B=b,
        T=par([TA,TB]),
        Name=simple-cases-parts.



rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([ recv(A, type(tyCon(ty__Ping)), ds_ddfZ),
                 cases(A, ds_ddfZ,
                       [ case(A, cstr__Ping(Q),
                              seq([ send(A, e_pid(Q), tyCon(ty__ProcessId),  A),
                                    recv(A, type(tyCon(ty__ABigRecord)), msg), 
				    cases(A, msg, [case(A, cstr__Foo(_, Ds_ddg7), assign(A, anf0, Ds_ddg7))], _),
				    assign(A, anf1, cstr__Unit),
                                    send(A, e_var(anf0), tyCon(ty__Tuple), anf1)]))
                       ],
				  default(A, die(A))
				 )
               ]),
        %%%%% proctype B:
        TB=seq([
		assign(B, anf0, cstr__Ping(B)),
		send(B, e_pid(A), tyCon(ty__Ping), anf0),
		recv(B, type(tyCon(ty__ProcessId)), q),
		assign(B, anf1, cstr__Foo(0, B)),
		send(B, e_var(q), tyCon(ty__ABigRecord), anf1),
		recv(B, type(tyCon(ty__Tuple)), q)
               ]),
	A=a, B=b,
        %%%%%
        T=par([TA,TB]),
        Name=simple-cases.

rewrite_query(T, skip, [], Name) :-
	T=par([
	       seq([
		    assign(A, anf0, cstr__SelfSigned(e_pid(A), e_pid(A))),
		    send(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), anf0) 
		   ]),
	       seq([
		    recv(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), msg) 
		   ])
	      ]),
	A=a,
	B=b,
	Name=de-casify-simple.





rewrite_query(T, skip, [], Name) :-
	T=par([
	       seq([
		    assign(A, anf0, cstr__SelfSigned(e_pid(A), A)),
		    send(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), anf0),
		    recv(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__Int)), msg)

		   ]),
	       seq([
		    recv(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), msg),	%,
		   
		    cases(B, msg, [
				   case(B, cstr__SelfSigned(X, Pay), assign(B, who, Pay))
				  ],
			  _),
		    ite(B, ndet, assign(B, anf1, 1), assign(B, anf1, 0)),
/*
		    cases(B, ndet, [
				    case(B, cstr__False, assign(B, anf1, 1)),
				    case(B, cstr__True, assign(B, anf1, 0))
				   ],
			  _),
*/		    
		    assign(B, blub, cstr__SelfSigned(e_pid(B), anf1)),
		    send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__Int)), blub)
		   
		   ])
	      ]),
	A=a,
	B=b,
	Name='de-casify'.




rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
                cases(A, act,
		      [ case(A, ping(Q),
			     send(A, e_pid(Q), pong, act)
			    ),
			case(A, pong(Q),
			     send(A, e_pid(Q), pong, act)
			    )
		      ],
		      skip)
               ]),
        %%%%% proctype B:
        TB=seq([ recv(B, var)]),
        %%%%%
        T=par([TA,TB]),
	A=a, B=b,
        Name=cases-simple-choice.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([send(m, e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2= seq([
		 assign(P, act, ping(m)),
		 cases(P, act,
		       [ case(P, ping(X),
			      seq([recv(P, id), send(P, e_pid(X), P)])
			     )
		       ], skip)
		]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
        Name=cases-split-loop.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([
		 send(m, e_pid(Q), m),
		 recv(m, e_pid(Q), x),
		 cases(m, x,
		       [
			case(m, ping(Proc), skip),
			case(m, pong(Proc), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 recv(P, id),
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 send(P, e_var(id), val)
		]),
	T=(par([seq([for(m, Q, s, P1)]), sym(P, s, P2)])),
        Name=case-cond-branch-loop.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P=p,
	P1=seq([
		 send(m, e_pid(P), m),
		 recv(m, e_pid(P), x),
		 cases(m, x,
		       [
			case(m, ping(_), skip),
			case(m, pong(_), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 recv(P, id),
		 send(P, e_var(id), val)
		]),
	T=(par([P1, P2])),
        Name=case-cond-branch.

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        T=par([TA,TB]),
        TA=seq([
		assign(A, ds_ddbB, cstr__Unit),
		for(A, _, set(B_Set),
		    seq([
			 recv(A, type(tyCon(ty__Lock)), ds_ddbG),
			 cases(A, ds_ddbG, [ case(A, cstr__Lock(P),
						  seq([
						      send(A, e_pid(P), tyCon(ty__Grant), cstr__Granted),
						      recv(A, e_pid(P), tyCon(ty__SelfSigned, tyCon(ty__Release)), msg),

						       cases(A, msg, [
								      case(A, cstr__SelfSigned(_, Pay), assign(A, ds_ddbD, Pay))
								     ],
							     skip),
						       cases(A, ds_ddbD, [
									  case(A, cstr__Release, assign(A, ds_ddbB, cstr__Unit))
									 ], skip)
						      ])
						 )
					   ], skip)
			])
		   )
	       ]),
	
        TB=sym(B, set(B_Set), seq([
				   assign(B, anf0, cstr__Lock(B)),
				   send(B, e_pid(A), tyCon(ty__Lock), anf0),
				   recv(B, type(tyCon(ty__Grant)), ds_ddbR),
				   assign(B, ds_ddbR, cstr__Granted),
				   cases(B, ds_ddbR, [
						      case(B, cstr__Granted,
							   seq([
								assign(B, anf1, cstr__SelfSigned(B, cstr__Release)),
								send(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__Release)), anf1)
							       ])
							  )
						     ], skip)
				  ])

	      ),
        A=a,
        B_Set=bs,
        Name=lock-server.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([ send(m, e_pid(Q), m) ]),
	P1B=seq([
		 recv(m, e_pid(s), x),
		 cases(m, x,
		       [
			case(m, ping(Proc), skip),
			case(m, pong(Proc), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 recv(P, id),
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 send(P, e_var(id), val)
		]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
        Name=cases-split-loop2.

rewrite_query(T,Rem,[], bakst-test) :-
	Rem=skip,
	T=par([
	       for(a, Ds_dcl2, b_Set, seq([
					   recv(a, type(tyCon(ty__ProcessId)), p),
					   send(a, e_var(p), tyCon(ty__Task), cstr__Done(null___))
					  ])
		  ),
	       sym(B, b_Set, seq([
				  assign(B, loop0, 1),
				  while(B, loop0=1, seq([
						       assign(B, loop0, 0),
						       send(B, e_pid(a), tyCon(ty__ProcessId), B),
						       recv(B, type(tyCon(ty__Task)), task),
						       cases(B, task, [
								       case(B, cstr__Done(null___), skip),
								       case(B, cstr__Work(ds_dclp),
									    assign(B, loop0, 1)
									   )
								      ],
							     skip)
						      ])
				       )
				 ])
		  )
	      ]).

rewrite_query(T,Rem, [], debakst-singleloop) :-
	Rem=sym(C,c_Set,TNLoop),
	T=par([For,sym(C,c_Set,seq([assign(C, loop0, 1),TNLoop]))]),
	For=
	for(a,
	    Tn, c_Set,
	    seq([
		 assign(a, tn, Tn), 
		 assign(a, anf3, cstr__GetTag(tid)), 
		 assign(a, anf2, cstr__Tuple(a, anf3)), 
		 send(a, e_var(tn),
		      tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)),
		      anf2), 
		 recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_) ,
		 cases(a,
		       msg_,
		       [
			case(a, cstr__SelfSigned(X, pay), assign(a, tag, pay))
		       ],
		       skip
		      ), 
		 cases(a,
		       tag,
		       [
			case(a, cstr__OK(null___), skip), 
			case(a, cstr__TagInfo(i), skip), 
			case(a, cstr__TagFound(t),
			     cases(a,
				   t,
				   [
				    case(a,
					 cstr__Tag(ds_dy80, ds_dy81, ds_dy82),
					 seq([
					      assign(a, dll__dll__brisk_anf_dyhF, ndet), 
					      cases(a,
						    dll__dll__brisk_anf_dyhF,
						    [
						     case(a,
							  cstr__Nothing(null___),
							  seq([
							       assign(a, anf4, cstr__Just(ndet)), 
							       assign(a, best, anf4)
							      ])
							 ), 
						     case(a,
							  cstr__Just(i),
							  seq([
							       assign(a, dll__dll__brisk_anf_dyhI, ndet), 
							       cases(a,
								     dll__dll__brisk_anf_dyhI,
								     [
								      case(a, cstr__False(null___), skip), 
								      case(a, cstr__True(null___),
									   seq([
										assign(a, anf5, cstr__Just(ndet)), 
										assign(a, best, anf5)
									       ])
									  )
								     ],
								     skip)
							      ])
							 )
						    ],
						    skip
						   )
					     ])
										     )
				   ], skip)), 
			case(a,
			     cstr__TagNotFound(null___),
			     skip
			    )
		       ],
		       skip
		      ) 
		])
	   ),
	TNLoop=while(C,
		     loop0=1,
		     seq([
			  assign(C, loop0, 0), 
			  recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deNr), 
			  cases(C,
				ds_deNr,
				[
				 case(C,
				      cstr__Tuple(who, msg),
				      seq([
					   assign(C, anf1, cstr__SelfSigned(C, cstr__OK(null___))), 
					   send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf1)
					  ])
				     )
				], skip), 
			  assign(C, st0, s_), 
			  assign(C, loop0, 1)
			 ])
		    ).

	
	

rewrite_query(T,Rem, [], debakst-filesystem) :- 
	While=
	while(a,
	      loop1=1,
	      seq([
		   assign(a, loop1, 0), 
		   recv(a, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI))), ds_deNr), 
		   cases(a,
			 ds_deNr,
			 [
			  case(a,
			       cstr__Tuple(who, msg),
			       seq([
				    cases(a,
					  msg,
					  [
					   case(a,
						cstr__AddBlob(ds_dy8D, ds_dy8E),
						seq([
						     assign(a, anf1, cstr__ReplyMsg(cstr__OK(null___), st0)), 
						     assign(a, reply, anf1)
						    ])
					       ), 
					   case(a,
						cstr__GetTag(tid),
						seq([
						     assign(a, best, cstr__Nothing(null___)),
						     for(a,
							 Tn, c_Set,
							 seq([
							      assign(a, tn, Tn), 
							      assign(a, anf3, cstr__GetTag(tid)), 
							      assign(a, anf2, cstr__Tuple(a, anf3)), 
							      send(a, e_var(tn),
								   tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)),
								   anf2), 
							      recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
							      cases(a,
								    msg_,
								    [
								     case(a, cstr__SelfSigned(X, pay), assign(a, tag, pay))
								    ],
								    skip
								   ), 
							      cases(a,
								    tag,
								    [
								     case(a, cstr__OK(null___), skip), 
								     case(a, cstr__TagInfo(i), skip), 
								     case(a, cstr__TagFound(t),
									  cases(a,
										t,
										[
										 case(a,
										      cstr__Tag(ds_dy80, ds_dy81, ds_dy82),
										      seq([
											   assign(a, dll__dll__brisk_anf_dyhF, ndet), 
											   cases(a,
												 dll__dll__brisk_anf_dyhF,
												 [
												  case(a,
												       cstr__Nothing(null___),
												       seq([
													    assign(a, anf4, cstr__Just(ndet)), 
													    assign(a, best, anf4)
													   ])
												      ), 
												  case(a,
												       cstr__Just(i),
												       seq([
													    assign(a, dll__dll__brisk_anf_dyhI, ndet), 
													    cases(a,
														  dll__dll__brisk_anf_dyhI,
														  [
														   case(a, cstr__False(null___), skip), 
														   case(a, cstr__True(null___),
															seq([
															     assign(a, anf5, cstr__Just(ndet)), 
															     assign(a, best, anf5)
															    ])
														       )
														  ],
														  skip)
													   ])
												      )
												 ],
												 skip
												)
											  ])
										     )
										], skip)), 
								     case(a,
									  cstr__TagNotFound(null___),
									  skip
									 )
								    ],
								    skip
								   )
							     ])
							),
						    cases(a,
							  res,
							  [
							    case(a,
								 cstr__Nothing(null___),
								 assign(a, anf6, cstr__Nil(null___))
								), 
							    case(a,
								 cstr__Just(z),
								 assign(a, anf6, ndet)
								)
							  ],
							  skip
							 ), 
						     assign(a, dll__dll__brisk_anf_dykO, anf6), 
						     assign(a, anf8, cstr__TagRefs(dll__dll__brisk_anf_dykO)), 
						     assign(a, anf7, cstr__ReplyMsg(anf8, st0)), 
						     assign(a, reply, anf7)])), 
					   case(a, cstr__AddTag(tag, refs), seq([
										 assign(a, anf9, cstr__ReplyMsg(cstr__OK(null___), st0)), 
										 assign(a, reply, anf9)
										])
					       )
					  ], skip
					 ), 
				    cases(a,
					  reply,
					  [
					   case(a,
						cstr__ReplyMsg(r, s_),
						seq([
						     assign(a, anf10, cstr__SelfSigned(a, r)), 
						     send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf10)
						    ])
					       ), 
					   case(a, cstr__NoReply(s_), skip)
					  ],
					  skip)
				   ])
			      )
			 ], skip
			), 
		   assign(a, st0, s_), 
		   assign(a, loop1, 1)
		  ])
	     ), 
	TNLoop=while(C,
		     loop0=1,
		     seq([
			  assign(C, loop0, 0), 
			  recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deNr), 
			  cases(C,
				ds_deNr,
				[
				 case(C,
				      cstr__Tuple(who, msg),
				      seq([
					   assign(C, anf1, cstr__SelfSigned(C, cstr__OK(null___))), 
					   send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf1)
					  ])
				     )
				], skip), 
			  assign(C, st0, s_), 
			  assign(C, loop0, 1)
			 ])
		    ),
	Rem=%While,
	par([
	     While,
	     sym(C,c_Set,TNLoop)
	    ]),
	T=par([
	       seq([
		    cases(a,
			  cstr__MS(ndet, ndet, 0),
			  [
			   case(a,
				cstr__MS(ds_dy93, ds_dy94, ds_dy95),
				assign(a, anf0, cstr__MS(ndet, c_Set, ds_dy95))
			       )
			  ],
			  skip
			 ), 
		    assign(a, dll__dll__brisk_anf_dyjU, anf0), 
		    assign(a, st0, dll__dll__brisk_anf_dyjU),
		    seq([
			 assign(a, loop1, 1),
			 While
			])
		   ]),
	       sym(C, c_Set, seq([
				  assign(C, dll__dll__brisk_anf_drrJ, ndet), 
				  assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drrJ)), 
				  assign(C, st0, anf0), 
				  seq([ assign(C, loop0, 1), TNLoop ])
				 ])
		  ),
	       sym(B, b_Set, seq([
				  assign(B, dll__dll__brisk_anf_d1n, ndet),
				  cases(B, dll__dll__brisk_anf_d1n, 
					[
					 case(B, cstr__False(null___),
					      assign(B, anf0, cstr__GetTag(cstr__TagId(ndet)))
					     ), 
					 case(B, cstr__True(null___),
					      assign(B, anf0, cstr__AddTag(cstr__TagId(ndet), ndet))
					     )
					 ],
					skip
				       ),
				 assign(B, rpc, anf0), 
				 assign(B, anf1, cstr__Tuple(B, rpc)),
				 %assign(B, anf1, cstr__Tuple(B, cstr__AddTag(cstr__TagId(ndet), ndet))),
				 %assign(B, anf1, cstr__Tuple(B, cstr__GetTag(cstr__TagId(ndet)))), 
				 send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf1), 
				  recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg) ,
				   cases(B,
					 msg,
					 [
					  case(B, cstr__SelfSigned(X, pay), assign(B, null, pay))
					 ], skip
					)
				 ])
		   )
	      ]).




rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		for(A, _, set(B_Set), seq([
					   recv(A, type(tyCon(ty__AcceptorResponse)), msg) %,
				      ])

		   ),
%		assign(A, ds_dbw4, cstr__Unit),
		for(A, X, set(B_Set),
%		    cases(A, ds_dbw4, [
%				       case(A, cstr__Unit, seq([ assign(A, anf1, cstr__Rollback(A)),
								 send(A, e_pid(X), tyCon(ty__CoordMessage), anf1) %]) )
%				      ],skip)
		   )

	       ]),
        TB=  sym(B, set(B_Set),
		 seq([
		      assign(B, ds_dbwi, cstr__Tuple(a, fn)),
		      cases(B, ds_dbwi,
			    [
			     case(B, cstr__Tuple(Who, Fn), seq([
								/*
								cases(B, ndet, [
										case(B, cstr__False,
										     assign(B, anf0, cstr__Reject)),
										case(B, cstr__True,
										     assign(B, anf0, cstr__Accept(B)))
									       ], skip
								     ),
								*/
								send(B, e_pid(a), tyCon(ty__AcceptorResponse), anf0),
								recv(B, type(tyCon(ty__CoordMessage)), msg)			
							       ])
				 )
			    ], skip)
		     ])
		),
        T=par([TA,TB]),
        A=a,
        B_Set=bs,
        Ind=[],
        Name=2-phase-commit-debug.


rewrite_query(T,Rem, [], bakst-smth) :-
	Rem=sym(B,
		b_Set,
		while(B, loop0=1, seq([
				       assign(B, loop0, 0), 
				       recv(B, type(tyCon(ty__Int)), r), 
				       cases(B,
					     dll__dll__brisk_anf_dj,
					     [
					      case(B,
						   cstr__False(null___),
						   assign(B, anf0, cstr__Unit(null___))
						  ), 
					      case(B,
						   cstr__True(null___),
						   assign(B, anf0, cstr__Unit(null___))
						  )
					     ], skip
					    ), 
				       assign(B, resp, anf0), 
				       assign(B, anf1, cstr__SelfSigned(B, resp)), 
				       send(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__Tuple)), anf1), 
				       assign(B, loop0, 1)
				      ])
		     )
	       ),
	T=par([ seq([ assign(a, d, 10), 
		      for(a, P, b_Set, seq([ assign(a, p, P), 
					     send(a, e_var(p), tyCon(ty__Int), d), 
					     recv(a, e_var(p), tyCon(ty__SelfSigned, tyCon(ty__Tuple)), msg), 
					     cases(a,
						   msg,
						   [
						    case(a, cstr__SelfSigned(X, pay), assign(a, null, pay))
						   ],
						   skip
						  )
					   ])
			 )
		    ]), 
		sym(B, b_Set, seq([ assign(B, loop0, 1), 
				    while(B, loop0=1,
					  seq([
					       assign(B, loop0, 0), 
					       recv(B, type(tyCon(ty__Int)), r), 
					       cases(B, dll__dll__brisk_anf_dj,
						     [
						      case(B, cstr__False(null___), assign(B, anf0, cstr__Unit(null___))), 
						      case(B, cstr__True(null___), assign(B, anf0, cstr__Unit(null___)))
						     ], skip
						    ), 
					       assign(B, resp, anf0), 
					       assign(B, anf1, cstr__SelfSigned(B, resp)), 
					       send(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__Tuple)), anf1), 
					       assign(B, loop0, 1)
					      ])
					 )
				  ])
		   )
	      ]).

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		assign(A, ds_dbw6, cstr__Unit),
		for(A, X, set(B_Set),
		     cases(A, ds_dbw6, [
					case(A, cstr__Unit,
					     seq([
						  assign(A, anf0, cstr__Tuple(A, fn)),
						  send(A, e_pid(X), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__String)), anf0)
						 ])
					    )
				       ], skip)
		    ),
	        assign(A, x, 0),
		for(A, _, set(B_Set), seq([
					   recv(A, type(tyCon(ty__AcceptorResponse)), msg),
					    cases(A, msg, [
							   case(A, cstr__Accept(bla), assign(A, x, ndet1)),
							   case(A, cstr__Reject, skip)
							  ], skip
						 )
				      ])

		   ),

		(
		  cases(A, ndet2, [
				 case(A, cstr(false), seq([
							   assign(A, ds_dbw4, cstr__Unit),
							   for(A, X, set(B_Set),
							       cases(A, ds_dbw4, [
										  case(A, cstr__Unit, seq([ assign(A, anf1, cstr__Rollback(A)),
													    send(A, e_pid(X), tyCon(ty__CoordMessage), anf1)]))
										 ],skip)
							      )
							  ])
				     ),
				 case(A, cstr(true), seq([
							  assign(A, ds_dbw2, cstr__Unit),
							  for(A, X, set(B_Set),
							      cases(A, ds_dbw2, [ case(A, cstr__Unit,
										       seq([
											    assign(A, anf2, cstr__Commit(A)),
											     send(A, e_pid(X), tyCon(ty__CoordMessage), anf2)]))
										], skip)
							     )
							 ])
				     )
				  ], skip)
		)
		]),
	       TB=sym(B, set(B_Set),
		      seq([
			   recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__String))), ds_dbwi),
			   cases(B, ds_dbwi,
				 [
				  case(B, cstr__Tuple(Who, Fn), seq([
								     
								     cases(B, ndet, [
										     case(B, cstr(false),
											  assign(B, anf0, cstr__Reject)),
										     case(B, cstr(true),
											  assign(B, anf0, cstr__Accept(B)))
										    ], skip
									  ),
								     send(B, e_pid(a), tyCon(ty__AcceptorResponse), anf0),
								     recv(B, type(tyCon(ty__CoordMessage)), msg) %,
								    /*
								     cases(B, msg, [
										    case(B, cstr__Commit(pid), assign(B, anf1, pid)),
										    case(B, cstr__Rollback(pid), assign(B, anf1, pid))
										   ], skip
									  ),
								     */
								     %send(B, e_var(anf1), tyCon(ty__AcceptorAck), cstr__ACK)
								    ])
				      )
			    ], skip)
		     ])
		),
        T=par([TA,TB]),
        A=a,
        B_Set=bs,
        Ind=[],
        Name=2-phase-commit.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([
		
		send(m, e_pid(p), bla(blub(y))),
		recv(m, e_pid(p), x)
	       ]),
	P2= seq([
		 recv(p, msg),
		 cases(p, msg,  [
				 case(p, bla(x),
				      cases(p, x, [
						   case(p, ducko(_), fail),
						   case(p, blub(_),
							send(p, e_pid(m), pong)
							)
						  ], skip
					   )
				      )
			  ],
		       skip)
		]),
	T=(par([P1,P2])),
        Name=case-split-on-msg.



rewrite_query(T,Rem, [], map-reduce-brisk) :-
	Rem=skip,
	T=par([
	       cases(a,
		     ds_d6xu,
		     [
		      case(a,
			   cstr__Tuple(node, nodes),
			   seq([
				assign(a, ds_d6xC, cstr__Unit(null___)), 
				iter(a,
				     global,
				     seq([
					  recv(a, type(tyCon(ty__Result)), ds_d6xD), 
					  cases(a, ds_d6xD, [
							     case(a,
								  cstr__Result(n),
								  assign(a, ds_d6xC, cstr__Unit(null___))
								 )
							    ],
						skip
					       )
					 ])
				    )
			       ])
			  )
		     ],
		     skip),
	       seq([
		    assign(b, ds_d7Eh, cstr__Unit(null___)), 
		    iter(b, global, seq([
					 recv(b, type(tyCon(ty__Request)), ds_d7Ei), 
					 cases(b, ds_d7Ei,
					       [
						case(b,
						     cstr__Request(mapperId),
						     seq([
							  assign(b, anf0, cstr__Work(a, i)), 
							  send(b, e_var(mapperId), tyCon(ty__Work), anf0)
							 ])
						    )
					       ],
					       skip
					      )
					])
			),
		    assign(b, ds_d7E3, cstr__Unit(null___)), 
		    for(b, X, c_Set, seq([ assign(b, x, X), 
					   recv(b, type(tyCon(ty__Request)), ds_d7E4), 
					   cases(b, ds_d7E4, [
							      case(b, cstr__Request(pid), send(b, e_var(pid), tyCon(ty__Work), cstr__Term(null___)))
							     ],
						 skip)
					 ])
		       )
		   ]), 
	       sym(C, c_Set, seq([
				  assign(C, loop0, 1), 
				  while(C, loop0=1, seq([ assign(C, loop0, 0), 
							  assign(C, anf0, cstr__Request(C)), 
							  send(C, e_pid(b), tyCon(ty__Request), anf0), 
							  recv(C, type(tyCon(ty__Work)), work), 
							  cases(C, work, [ case(C,
										cstr__Work(master, i),
										seq([
										     assign(C, anf1, cstr__Result(i)), 
										     send(C, e_pid(a), tyCon(ty__Result), anf1), 
										     assign(C, loop0, 1)
										    ])
									       ), 
									   case(C, cstr__Term(null___), skip)
									 ],
								skip
							       )
							])
				       )
				 ])
		  )
	      ]).

rewrite_query(T, sym(P,set, While), Ind, Name) :-
	Ind=[],

	P1=seq([
		nondet(Q, set, assign(m, pid, Q)),
		send(m, e_var(pid), m),
		recv(m, e_var(pid), x)
		]),
	P2A= seq([
		 recv(P, id),
		 send(P, e_var(id), val)
		 ]),
	While=while(P, true, P2A),
	P2=sym(P, set, seq([assign(P,x,some),While])),
	T=(par([P1,P2])),
	
        Name=remove-assign-ex.

rewrite_query(T, P2, Ind, Name) :-
	Ind=[],
	P1=seq([
		nondet(Q, set, assign(m, pid, Q)),
		       seq([
			    send(m, e_var(pid), m),
			    recv(m, e_var(pid), x)
			   ])
		]),
	P2A= seq([
		 recv(P, id),
		 send(P, e_var(id), val)
		]),
	P2=sym(P, set, while(P, true, P2A)),
	T=(par([P1,P2])),
        Name=send-to-nondet.

rewrite_query(T, P2, [], bakst1) :- R=skip,
	T=par([ seq([
		     recv(a, type(tyCon(ty__PingMessage)), msg),
		     cases(a, msg, [
				    case(a, cstr__Ping(Whom),
					 seq([
					      assign(a, anf0, cstr__Pong(a)),
					      send(a, e_pid(Whom), tyCon(ty__PingMessage), anf0)
					     ])
					),
				    case(a, cstr__Pong(X), seq([
								assign(a, anf1, cstr__Ping(a)),
								send(a, e_pid(X), tyCon(ty__PingMessage), anf1)
							       ])
					)
				   ], skip)
		    ]),
		seq([
		     assign(b,x,cstr__False),
		     cases(b, x, [
				  case(b, cstr__False, seq([
							    assign(b, anf0, cstr__Ping(b)),
							    send(b, e_pid(a), tyCon(ty__PingMessage), anf0)
							   ])
				      ),
                                case(b, cstr__True, seq([ assign(b, anf1, cstr__Ping(b)),
                                                          send(b, e_pid(a), tyCon(ty__PingMessage), anf1)
							])
				    )
				 ], skip),
		     recv(b, type(tyCon(ty__PingMessage)), dev_null__)
		    ])
	      ]).

rewrite_query(T,Rem,[],file-system) :- Rem=sym(B, b_Set, while(B, loop0=1, seq([ assign(B, loop0, 0), 
                                      recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI))), ds_deMH), 
                                      cases(B, ds_deMH, [ case(B, cstr__Tuple(who, msg), seq([ cases(B, msg, [ case(B, cstr__AddBlob(bn, blob), seq([ assign(B, dll__dll__brisk_anf_du0Y, ndet), 
                                                                                                                                                      cases(B, dll__dll__brisk_anf_du0Y, [ case(B, cstr__Nothing(null___), assign(B, anf1, cstr__Tuple(cstr__OK(null___), cases(B, st0, [ case(B, cstr__DNS(ds_dtUR), cstr__DNS(ndet))], skip)))), 
                                                                                                                                                                                           case(B, cstr__Just(ds_dtV3), assign(B, anf1, cstr__Tuple(cstr__BlobExists(null___), st0)))], skip), 
                                                                                                                                                      assign(B, ds_dtV4, anf1), 
                                                                                                                                                      cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf2, response))], skip), 
                                                                                                                                                      assign(B, response, anf2), 
                                                                                                                                                      cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf3, st_))], skip), 
                                                                                                                                                      assign(B, st_, anf3), 
                                                                                                                                                      assign(B, dll__dll__brisk_anf_du18, response), 
                                                                                                                                                      assign(B, dll__dll__brisk_anf_du1a, st_), 
                                                                                                                                                      assign(B, anf4, cstr__ReplyMsg(dll__dll__brisk_anf_du18, dll__dll__brisk_anf_du1a)), 
                                                                                                                                                      assign(B, reply, anf4)])), 
                                                                                                               case(B, cstr__GetBlob(bid), seq([ assign(B, dll__dll__brisk_anf_du1e, ndet), 
                                                                                                                                                 cases(B, dll__dll__brisk_anf_du1e, [ case(B, cstr__Nothing(null___), assign(B, anf5, cstr__BlobNotFound(null___))), 
                                                                                                                                                                                      case(B, cstr__Just(bdata), assign(B, anf5, cstr__BlobData(bdata)))], skip), 
                                                                                                                                                 assign(B, dll__dll__brisk_anf_du1g, anf5), 
                                                                                                                                                 assign(B, anf6, cstr__ReplyMsg(dll__dll__brisk_anf_du1g, st0)), 
                                                                                                                                                 assign(B, reply, anf6)]))], skip), 
                                                                                               cases(B, reply, [ case(B, cstr__ReplyMsg(r, s_), seq([ assign(B, anf7, cstr__SelfSigned(B, r)), 
                                                                                                                                                      send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf7)])), 
                                                                                                                 case(B, cstr__NoReply(s_), skip)], skip)]))], skip), 
                                      assign(B, st0, s_), 
                                      assign(B, loop0, 1)]))),
T=par([ seq([ assign(a, dll__dll__brisk_anf_d1A, ndet), 
            cases(a, dll__dll__brisk_anf_d1A, [ case(a, cstr__False(null___), assign(a, anf0, cstr__GetBlob(ndet))), 
                                                case(a, cstr__True(null___), assign(a, anf0, cstr__AddBlob(ndet, ndet)))], skip), 
            assign(a, rpc, anf0), 
            nondet(D, b_Set, assign(a, d, D)), 
            assign(a, anf1, cstr__Tuple(a, rpc)), 
            send(a, e_var(d), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI)), anf1), 
            recv(a, e_var(d), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), msg), 
            cases(a, msg, [ case(a, cstr__SelfSigned(X, pay), assign(a, _, pay))], skip)]), 
      sym(B, b_Set, seq([ assign(B, dll__dll__brisk_anf_du08, ndet), 
                          assign(B, anf0, cstr__DNS(dll__dll__brisk_anf_du08)), 
                          assign(B, st0, anf0), 
                          seq([ assign(B, loop0, 1), 
                                while(B, loop0=1, seq([ assign(B, loop0, 0), 
                                                        recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI))), ds_deMH), 
                                                        cases(B, ds_deMH, [ case(B, cstr__Tuple(who, msg), seq([ cases(B, msg, [ case(B, cstr__AddBlob(bn, blob), seq([ assign(B, dll__dll__brisk_anf_du0Y, ndet), 
                                                                                                                                                                        cases(B, dll__dll__brisk_anf_du0Y, [ case(B, cstr__Nothing(null___), assign(B, anf1, cstr__Tuple(cstr__OK(null___), cases(B, st0, [ case(B, cstr__DNS(ds_dtUR), cstr__DNS(ndet))], skip)))), 
                                                                                                                                                                                                             case(B, cstr__Just(ds_dtV3), assign(B, anf1, cstr__Tuple(cstr__BlobExists(null___), st0)))], skip), 
                                                                                                                                                                        assign(B, ds_dtV4, anf1), 
                                                                                                                                                                        cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf2, response))], skip), 
                                                                                                                                                                        assign(B, response, anf2), 
                                                                                                                                                                        cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf3, st_))], skip), 
                                                                                                                                                                        assign(B, st_, anf3), 
                                                                                                                                                                        assign(B, dll__dll__brisk_anf_du18, response), 
                                                                                                                                                                        assign(B, dll__dll__brisk_anf_du1a, st_), 
                                                                                                                                                                        assign(B, anf4, cstr__ReplyMsg(dll__dll__brisk_anf_du18, dll__dll__brisk_anf_du1a)), 
                                                                                                                                                                        assign(B, reply, anf4)])), 
                                                                                                                                 case(B, cstr__GetBlob(bid), seq([ assign(B, dll__dll__brisk_anf_du1e, ndet), 
                                                                                                                                                                   cases(B, dll__dll__brisk_anf_du1e, [ case(B, cstr__Nothing(null___), assign(B, anf5, cstr__BlobNotFound(null___))), 
                                                                                                                                                                                                        case(B, cstr__Just(bdata), assign(B, anf5, cstr__BlobData(bdata)))], skip), 
                                                                                                                                                                   assign(B, dll__dll__brisk_anf_du1g, anf5), 
                                                                                                                                                                   assign(B, anf6, cstr__ReplyMsg(dll__dll__brisk_anf_du1g, st0)), 
                                                                                                                                                                   assign(B, reply, anf6)]))], skip), 
                                                                                                                 cases(B, reply, [ case(B, cstr__ReplyMsg(r, s_), seq([ assign(B, anf7, cstr__SelfSigned(B, r)), 
                                                                                                                                                                        send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf7)])), 
                                                                                                                                   case(B, cstr__NoReply(s_), skip)], skip)]))], skip), 
                                                        assign(B, st0, s_), 
                                                        assign(B, loop0, 1)]))])]))]).


rewrite_query(T,Rem,[], full-fs) :- Rem=sym(B, b_Set, while(B, loop0=1, seq([ assign(B, loop0, 0), 
                                      recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI))), ds_deMH), 
                                      cases(B, ds_deMH, [ case(B, cstr__Tuple(who, msg), seq([ cases(B, msg, [ case(B, cstr__AddBlob(bn, blob), seq([ assign(B, dll__dll__brisk_anf_du0Y, ndet), 
                                                                                                                                                      cases(B, dll__dll__brisk_anf_du0Y, [ case(B, cstr__Nothing(null___), assign(B, anf1, cstr__Tuple(cstr__OK(null___), cases(B, st0, [ case(B, cstr__DNS(ds_dtUR), cstr__DNS(ndet))], skip)))), 
                                                                                                                                                                                           case(B, cstr__Just(ds_dtV3), assign(B, anf1, cstr__Tuple(cstr__BlobExists(null___), st0)))], skip), 
                                                                                                                                                      assign(B, ds_dtV4, anf1), 
                                                                                                                                                      cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf2, response))], skip), 
                                                                                                                                                      assign(B, response, anf2), 
                                                                                                                                                      cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf3, st_))], skip), 
                                                                                                                                                      assign(B, st_, anf3), 
                                                                                                                                                      assign(B, dll__dll__brisk_anf_du18, response), 
                                                                                                                                                      assign(B, dll__dll__brisk_anf_du1a, st_), 
                                                                                                                                                      assign(B, anf4, cstr__ReplyMsg(dll__dll__brisk_anf_du18, dll__dll__brisk_anf_du1a)), 
                                                                                                                                                      assign(B, reply, anf4)])), 
                                                                                                               case(B, cstr__GetBlob(bid), seq([ assign(B, dll__dll__brisk_anf_du1e, ndet), 
                                                                                                                                                 cases(B, dll__dll__brisk_anf_du1e, [ case(B, cstr__Nothing(null___), assign(B, anf5, cstr__BlobNotFound(null___))), 
                                                                                                                                                                                      case(B, cstr__Just(bdata), assign(B, anf5, cstr__BlobData(bdata)))], skip), 
                                                                                                                                                 assign(B, dll__dll__brisk_anf_du1g, anf5), 
                                                                                                                                                 assign(B, anf6, cstr__ReplyMsg(dll__dll__brisk_anf_du1g, st0)), 
                                                                                                                                                 assign(B, reply, anf6)]))], skip), 
                                                                                               cases(B, reply, [ case(B, cstr__ReplyMsg(r, s_), seq([ assign(B, anf7, cstr__SelfSigned(B, r)), 
                                                                                                                                                      send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf7)])), 
                                                                                                                 case(B, cstr__NoReply(s_), skip)], skip)]))], skip), 
                                      assign(B, st0, s_), 
                                      assign(B, loop0, 1)]))),
T=par([ seq([ assign(a, dll__dll__brisk_anf_d1A, ndet), 
            cases(a, dll__dll__brisk_anf_d1A, [ case(a, cstr__False(null___), assign(a, anf0, cstr__GetBlob(ndet))), 
                                                case(a, cstr__True(null___), assign(a, anf0, cstr__AddBlob(ndet, ndet)))], skip), 
            assign(a, rpc, anf0), 
            nondet(D, b_Set, assign(a, d, D)), 
            assign(a, anf1, cstr__Tuple(a, rpc)), 
            send(a, e_var(d), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI)), anf1), 
            recv(a, e_var(d), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), msg), 
            cases(a, msg, [ case(a, cstr__SelfSigned(X, pay), assign(a, _, pay))], skip)]), 
      sym(B, b_Set, seq([ assign(B, dll__dll__brisk_anf_du08, ndet), 
                          assign(B, anf0, cstr__DNS(dll__dll__brisk_anf_du08)), 
                          assign(B, st0, anf0), 
                          seq([ assign(B, loop0, 1), 
                                while(B, loop0=1, seq([ assign(B, loop0, 0), 
                                                        recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI))), ds_deMH), 
                                                        cases(B, ds_deMH, [ case(B, cstr__Tuple(who, msg), seq([ cases(B, msg, [ case(B, cstr__AddBlob(bn, blob), seq([ assign(B, dll__dll__brisk_anf_du0Y, ndet), 
                                                                                                                                                                        cases(B, dll__dll__brisk_anf_du0Y, [ case(B, cstr__Nothing(null___), assign(B, anf1, cstr__Tuple(cstr__OK(null___), cases(B, st0, [ case(B, cstr__DNS(ds_dtUR), cstr__DNS(ndet))], skip)))), 
                                                                                                                                                                                                             case(B, cstr__Just(ds_dtV3), assign(B, anf1, cstr__Tuple(cstr__BlobExists(null___), st0)))], skip), 
                                                                                                                                                                        assign(B, ds_dtV4, anf1), 
                                                                                                                                                                        cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf2, response))], skip), 
                                                                                                                                                                        assign(B, response, anf2), 
                                                                                                                                                                        cases(B, ds_dtV4, [ case(B, cstr__Tuple(response, st_), assign(B, anf3, st_))], skip), 
                                                                                                                                                                        assign(B, st_, anf3), 
                                                                                                                                                                        assign(B, dll__dll__brisk_anf_du18, response), 
                                                                                                                                                                        assign(B, dll__dll__brisk_anf_du1a, st_), 
                                                                                                                                                                        assign(B, anf4, cstr__ReplyMsg(dll__dll__brisk_anf_du18, dll__dll__brisk_anf_du1a)), 
                                                                                                                                                                        assign(B, reply, anf4)])), 
                                                                                                                                 case(B, cstr__GetBlob(bid), seq([ assign(B, dll__dll__brisk_anf_du1e, ndet), 
                                                                                                                                                                   cases(B, dll__dll__brisk_anf_du1e, [ case(B, cstr__Nothing(null___), assign(B, anf5, cstr__BlobNotFound(null___))), 
                                                                                                                                                                                                        case(B, cstr__Just(bdata), assign(B, anf5, cstr__BlobData(bdata)))], skip), 
                                                                                                                                                                   assign(B, dll__dll__brisk_anf_du1g, anf5), 
                                                                                                                                                                   assign(B, anf6, cstr__ReplyMsg(dll__dll__brisk_anf_du1g, st0)), 
                                                                                                                                                                   assign(B, reply, anf6)]))], skip), 
                                                                                                                 cases(B, reply, [ case(B, cstr__ReplyMsg(r, s_), seq([ assign(B, anf7, cstr__SelfSigned(B, r)), 
                                                                                                                                                                        send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf7)])), 
                                                                                                                                   case(B, cstr__NoReply(s_), skip)], skip)]))], skip), 
                                                        assign(B, st0, s_), 
                                                        assign(B, loop0, 1)]))])]))]).

rewrite_query(T, sym(B, b_Set, While), [], Name) :-
	Name=bakst2,
	T=par([
	       seq([
		     nondet(P0, b_Set, assign(a, p0, P0)),
		     send(a, e_var(p0), tyCon(ty__Tuple), cstr__Unit),
		     recv(a, e_var(p0), tyCon(ty__SelfSigned, tyCon(ty__Int)), msg),
		     cases(a, msg, [
				    case(a,
					 cstr__SelfSigned(_, Pay), assign(a, _, Pay)
					)
				   ], skip)
		   ]),
	       sym(B, b_Set,	  
		   seq([
			assign(B, me_, le_me),
			assign(B, loop0, true),
			While
		       ])
		   )
	      ]),
	While=while(B, loop0, seq([
				  assign(B, loop0, true),
				  recv(B, type(tyCon(ty__Tuple)), dev_null__),
				  assign(B, anf0, cstr__SelfSigned(B, 0)),
				  send(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__Int)), anf0),
				 assign(B, loop0, true)
				 ])
		   ).


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	Name=bakst,
	T=par([ seq([ recv(a, type(tyCon(ty__PingMessage)), msg),
		      cases(a, msg, [ case(a, cstr__Ping(Whom), seq([
								     assign(a, anf0, cstr__Pong(a)),
								     send(a, e_pid(Whom), tyCon(ty__PingMessage), anf0)])
					  ),
                            case(a, cstr__Pong(X), seq([ assign(a, anf1, cstr__Ping(a)),
                                                         send(a, e_pid(X), tyCon(ty__PingMessage), anf1)
						       ])
				)
				    ], skip)
		    ]),
		seq([ assign(b, anf0, cstr__Ping(b)),
		      send(b, e_pid(a), tyCon(ty__PingMessage), anf0),
		      recv(b, type(tyCon(ty__PingMessage)), zoog)
		    ])
	      ]).

rewrite_query(par([T1,T2]), skip, Ind, Name) :-
	Ind=[],
	Name=cases-loop-free,
	T1=seq([cases(a,
		      msg,
		      [ 
			case(a, cstr__Tuple(a, type),
			     seq([
			     cases(a,
				   type,
				   [
				    case(a,
					 cstr__GetBlob(ndet), seq([
								   assign(a, rpc, msg)
								  ])
					),
				    case(a,
					 cstr__AddBlob(ndet, ndet), seq([
									 assign(a, rpc, msg)
									])
					)
				   ], skip),
				  send(a, e_pid(p), rpc),
				  cases(a, type, [
						 case(a, cstr__GetBlob(bla1), skip),
						 case(a, cstr__AddBlob(bla2, bla3), recv(a, val))
						],
					skip)
				 ])
			    )
		      ], skip)
	       ]),
	T2= seq([
		 recv(p, rpc),
		 cases(p, rpc,
		       [
			case(p, cstr__Tuple(pid, payload),
			     cases(p, payload, [
						case(p, cstr__AddBlob(bla1,bla2), send(p, e_var(pid), blob)),
						case(p, cstr__GetBlob(bla3), skip)
					       ], skip)
			    )
		       ],skip)
		]).
%% proctype a:
%%   $$brisk_anf_d8an := {_ ∈ %b_Set}
%%   anf1 := (AddBlob({@Process String},{@Process ByteString}))
%%   anf0 := (Tuple(%a,anf1))
%%   send[Tuple[ProcessId DataNodeAPI]]($$brisk_anf_d8an,anf0)
%%   msg := recvFrom[SelfSigned[DataNodeResponse]]($$brisk_anf_d8an)
%%   match msg:
%%     case (SelfSigned(_,pay)):
%%       _ := pay
%% proctype (B:b_Set):
%%   $$brisk_anf_du2J := {@HashMap[BlobId ByteString]}
%%   anf0 := (DNS($$brisk_anf_du2J))
%%   st0 := anf0
%%   while true:
%%     ds_ddBx := recv[Tuple[ProcessId DataNodeAPI]]
%%     match ds_ddBx:
%%       case (Tuple(who,msg)):
%%         match msg:
%%           case (AddBlob(bn,blob)):
%%             $$brisk_anf_du3J := {@Bool}
%%             match $$brisk_anf_du3J:
%%               case False:
%%                 resp := BlobExists
%%               case True:
%%                 resp := OK
%%             anf1 := (ReplyMsg(resp,st0))
%%             reply := anf1
%%           case (GetBlob(bid)):
%%             anf2 := (ReplyMsg(BlobExists,st0))
%%             reply := anf2
%%         match reply:
%%           case (ReplyMsg(r,s')):
%%             anf3 := (SelfSigned(B,r))
%%             send[SelfSigned[DataNodeResponse]](who,anf3)
%%           case (NoReply(s')):
%%             skip
%%     st0 := s'
%%     continue
rewrite_query(T,Rem,[],bakst-fs) :-
	Rem=sym(B, b_Set, While),
        While=while(B, loop0=1,
                    seq([ assign(B, loop0, 0), 
                          recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI))), ds_ddBx), 
                          cases(B, ds_ddBx,
                                [ case(B, cstr__Tuple(who, msg),
                                       seq([ cases(B, msg,
                                                   [ case(B, cstr__AddBlob(bn, blob),
                                                          seq([ assign(B, dll__dll__brisk_anf_du3J, ndet), 
                                                                cases(B, dll__dll__brisk_anf_du3J,
                                                                      [ case(B, cstr__False(null___), assign(B, resp, cstr__BlobExists(null___))), 
                                                                        case(B, cstr__True(null___), assign(B, resp, cstr__OK(null___)))], skip), 
                                                                assign(B, anf1, cstr__ReplyMsg(resp, st0)), 
                                                                assign(B, reply, anf1)])), 
                                                     case(B, cstr__GetBlob(bid),
                                                          seq([ assign(B, anf2, cstr__ReplyMsg(cstr__BlobExists(null___), st0)), 
                                                                assign(B, reply, anf2)]))], skip), 
                                             cases(B, reply, [ case(B, cstr__ReplyMsg(r, s_),
                                                                    seq([ assign(B, anf3, cstr__SelfSigned(B, r)), 
                                                                          send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf3)])), 
                                                               case(B, cstr__NoReply(s_), skip)], skip)]))], skip), 
                          assign(B, st0, s_), 
                          assign(B, loop0, 1)])),
        T=par([ seq([
		     nondet(D, b_Set, assign(a, d, D)), 
		     assign(a, anf1, cstr__AddBlob(ndet, ndet)), 
		     assign(a, anf0, cstr__Tuple(a, anf1)), 
		     send(a, e_var(d), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI)), anf0), 
		     recv(a, e_var(d), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), msg), 
		     cases(a, msg, [ case(a, cstr__SelfSigned(_, pay), assign(a, _, pay))], skip)]), 
                sym(B, b_Set, seq([ assign(B, dll__dll__brisk_anf_du2J, ndet), 
                                    assign(B, anf0, cstr__DNS(dll__dll__brisk_anf_du2J)), 
                                    assign(B, st0, anf0), 
                                    seq([ assign(B, loop0, 1), While ])]))]).

rewrite_query(par([T,While]),Rem,[], bakst-minimal) :- Rem=skip,
	B=b,
        While=seq([ 
		    recv(B,  ds_ddBx), 
		    cases(B, ds_ddBx,
			  [
			   case(B, cstr__Tuple(who, msg),
				seq([ cases(B, msg,
					    [ case(B, cstr__AddBlob(bn, blob),
						   seq([ 
							 cases(B, dll__dll__brisk_anf_du3J,
							       [ case(B, cstr__False(null___),
								      skip), 
								 case(B, cstr__True(null___),
								      skip)
							       ], skip)
						       ])
						  ), 
					      case(B, cstr__GetBlob(bid),
						   skip
						  )],
					    skip),
				      send(B, e_var(who), anf3)
				    ])
			       )], skip)
		  ]),
        T=seq([
	       assign(a, d, b),
	       send(a, e_var(d),  cstr__Tuple(a, msg)), 
	       recv(a, e_var(d), msg)
	      ]).	


rewrite_query(par([T,While]),Rem,[], bakst-test2) :- Rem=skip,
	B=b,
        While=seq([ 
		    recv(B,  ds_ddBx), 
		    cases(B, ds_ddBx,
		    [ case(B, cstr__Tuple(who, msg),
			   seq([ cases(B, msg,
				       [ case(B, cstr__AddBlob(bn, blob),
					      seq([ 
						    cases(B, dll__dll__brisk_anf_du3J,
							  [ case(B, cstr__False(null___),
								 assign(B, resp, cstr__Blob__Exists(null___))), 
							    case(B, cstr__True(null___),
								 assign(B, resp, cstr__OK(null___)
								       )
								)
							  ], skip),
						    assign(B, anf1, cstr__ReplyMsg(resp, st0)), 
						    assign(B, reply, anf1)])
					     ), 
					 case(B, cstr__GetBlob(bid),
					      seq([ assign(B, anf2, cstr__ReplyMsg(cstr__BlobExists(null___), st0)), 
						    assign(B, reply, anf2)])
					     )],
				       skip), 
				 cases(B, reply, [
						  case(B, cstr__ReplyMsg(r, s_),
						       seq([
							    assign(B, anf3, cstr__SelfSigned(B, r)), 
							    send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), anf3)
							   ])
						      ), 
						  case(B, cstr__NoReply(s_), skip)],
				       skip)
			       ])
			  )], skip)
	    ]),
        T=seq([
	       assign(a, d, b),
	       assign(a, anf1, cstr__AddBlob(ndet, ndet)), 
	       assign(a, anf0, cstr__Tuple(a, anf1)), 
	       send(a, e_var(d), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__DataNodeAPI)), anf0), 
	       recv(a, e_var(d), tyCon(ty__SelfSigned, tyCon(ty__DataNodeResponse)), msg)
	      ]).

/* Annotations */
rewrite_query(T, skip, [], simple-annots) :-
	P1=seq([send(m, e_pid(Q), m), recv(m, e_pid(Q), x)]),
	P2=seq([recv(P, e_pid(m), id), send(P,e_pid(m),P)]),
	T=(par([for(m, Q, s, rr, Inv, P1), sym(P, s, P2)])),
    Inv=true,
	Name=simple-ping-loop.
/*
rewrite_query(par([T1,T2]), T2, Ind, Name) :-
	Ind=[],
	Name=file-system1,
	T1=seq([cases(a,
		      msg,
		      [ 
			case(a, cstr__Tuple(a, type),
			     seq([
			     cases(a,
				   type,
				   [
				    case(a,
					 cstr__GetBlob(ndet), seq([
								   assign(a, rpc, msg)
								  ])
					),
				    case(a,
					 cstr__AddBlob(ndet, ndet), seq([
									 assign(a, rpc, msg)
									])
					)
				   ], skip),
				  nondet(P, set(b_Set), assign(a, pid, P)),
				  send(a, e_var(pid), rpc),
				  cases(a, type, [
						 case(a, cstr__GetBlob(bla1), skip),
						 case(a, cstr__AddBlob(bla2, bla3), recv(a, e_var(pid), val))
						],
					skip)
				 ])
			    )
		      ], skip)
	       ]),
	T2= sym(B, set(b_Set), while(B, true,
				     seq([
					  recv(B, e_pid(a), rpc),
					  cases(B, rpc,
						[
						 case(B, cstr__Tuple(pid, payload),
						      cases(B, payload, [
									 case(B, cstr__AddBlob(bla1,bla2),
									      send(B, e_var(pid), blob)
									     ),
									 case(B, cstr__GetBlob(bla3), skip)
									], skip)
						     )
						],skip)
					 ])
				    )
	       ).
*/
/*
rewrite_query(par([T1,T2]), T2, Ind, Name) :-
	Ind=[],
	Name=cases-match-ndet-send,
	T1=seq([cases(a,
		      msg,
		      [ 
			case(a, cstr__Tuple(a, Type),
			     seq([
			     cases(a,
				   Type,
				   [
				    case(a,
					 cstr__GetBlob(ndet), seq([
								   assign(a, rpc, msg)
								  ])
					),
				    case(a,
					 cstr__AddBlob(ndet, ndet), seq([
									 assign(a, rpc, msg)
									])
					)
				   ], skip),
				  nondet(P, set(b_Set),
					 seq([
					      send(a, e_pid(P), rpc),
					      cases(a, rpc, [
							    case(a, cstr__Tuple(_,cstr__AddBlob(_, _)), recv(a, e_pid(P), val)),
							    case(a, cstr__Tuple(_,cstr__GetBlob(_)), skip)
							   ],
						   skip)
					     ])
					)
				 ])
			    )
		      ], skip)
	       ]),
	T2= sym(B, set(b_Set), while(B, true, seq([
						   recv(B, ds_dfg0),
						   cases(B, ds_dfg0,
							 [
							  case(B, cstr__Tuple(PID, Ds_d8vq),
							       cases(B, Ds_d8vq, [
										  case(B, cstr__AddBlob(_, _), send(B, e_pid(PID), bla)),
										  case(B, cstr__GetBlob(_), skip)
										 ], skip)
							      )
							 ],skip)
						  ])
				    )
		).
*/
