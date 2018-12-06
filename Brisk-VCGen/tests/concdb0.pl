prog(simple, 

     [ decl(s,set)
     , decl(workSet,set)
     , decl(dbproc,int)

     , decl(x,map(set(s),int))
     , decl(v,map(set(s),int))
     , decl(t,map(set(s),int))
     , decl(vv,map(set(s),int))
     , decl(id,map(set(s),int))
     , decl(status,map(set(s),int))

     , decl(k,int)
     , decl(valu,int)
     , decl(response, int)
     , decl(tag,int)
     , decl(domain,map(int,int))
     , decl(db,map(int,int))
     ], 

     ensures(true), 
     
     sym(C, s, true,
         iter(workSet, true,
           atomic(seq([pre(C, true)
                         , ite(C, ref(status,C)=1
                         , seq([ assign(dbproc, pair(tag, k, valu), pair(1, ref(x,C), 0))
                               , ite(dbproc, sel(domain,k)=1
                                    , assign(dbproc, pair(tag, response), pair(1, sel(db,k)))
                                    , assign(dbproc, pair(tag, response), pair(0, 0)))
                               , assign(C, pair(t, vv), pair(tag, response))
                               , pre(C, forall([decl(i,int)], implies(elem(i,s), ref(vv,i)=ref(v,i))))
                              ])
                         , skip)
                    ]))))).
            
