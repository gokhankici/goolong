prog(simple, Vars, ensures(Property), Program) :-
      Vars=[ decl(s, set)
           , decl(m, int)
           , decl(id, map(set(s), int))
           ]

    , Property=forall([decl(p,int)], implies(elem(p,s), ref(id, p)=m))

    , Program=par([for(m, Q, s, rr, LoopInv, P1), sym(P, s, P2)])
      
    , LoopInv=forall([decl(p,int)], implies(elem(p,rr), ref(id, p)=m))

    , P1=seq([send(m, e_pid(Q), m)])
	, P2=seq([recv(P, e_pid(m), id), assign(P, id, 0)])
.
