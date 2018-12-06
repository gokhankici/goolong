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
         iter(workSet, true, seq([
           atomic(seq([
               assign(dbproc,pair(tag, k, valu), pair(0, ref(x,C), ref(v,C)))
             , ite(dbproc,sel(domain,ref(x,C))=1
                  , assign(dbproc,response,0)
                  , seq([ assign(dbproc,response,1)
                        , assign(dbproc,domain,upd(domain,k,1))
                        , assign(dbproc,db,upd(db,k,valu))
                        ]))
            , assign(C,status,response)
           ]))
           , atomic(seq([pre(C,forall([decl(i,int)],
                                        implies(and([here(i), elem(i,s), ref(status,i)=1])
                                              , and([sel(db,ref(x,i))=ref(v,i),sel(domain,ref(x,i))=1]))))
                         , ite(C, ref(status,C)=1
                                , seq([ assign(dbproc, pair(tag, k, valu), pair(1, ref(x,C), 0))
                                      , assert(C, sel(db,ref(x,C))=ref(v,C))
                                      , ite(dbproc, sel(domain,k)=1
                                           , assign(dbproc, pair(tag, response), pair(1, sel(db,k)))
                                           , assign(dbproc, pair(tag, response), pair(0, 0)))
                                      , assign(C, pair(t, vv), pair(tag, response))
                                     ])
                                , skip)
                    ]))])))).
            
