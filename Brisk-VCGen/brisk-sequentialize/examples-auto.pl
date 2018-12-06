
rewrite_query(T,skip,[],Name) :-
	T = par([
		 seq([
		      send(p0,e_pid(p1),tapp(mastermsg,pid),p0),
		      for(p0, XL1, set(r2),
			  seq([
			       send(p0,e_pid(XL1),tapp(mastermsg,pid),p1)
			      ])
			 ),
		      recv(p0,type(unit),x4)
		     ]),
		 seq([
		      recv(p1,type(tapp(mastermsg,pid)),x1),
		      for(p1,XL2,set(r2),seq([
					      recv(p1,type(tapp(clientmsg,pid)),x2)
					     ])
			 ),
		      send(p1,e_var(x1),unit,e_tt)
		     ]),
		 sym(IR2, set(r2),seq([
				      recv(IR2,type(tapp(mastermsg,pid)),x3),
				      send(IR2,e_var(x3),tapp(clientmsg,pid),IR2)
				     ])
		    )
		]),
    Name = registry.

rewrite_query(T,par([while(p1,true,seq([recv(p1,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x11,pair(x13,x14))),ite(p1,x11 = 0,seq([nondet(x17,set(r2)),send(p1,e_pid(x17),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(0,x12))]),seq([nondet(X20,set(r2)),send(p1,e_pid(X20),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,x12))]))])),while(ir2,true,seq([recv(ir2,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x4,pair(x6,x7))),ite(ir2,x4 = 0,seq([seq([assign(ir2,e1,1),while(ir2,e1 = 1,seq([assign(ir2,e1,0),skip]))]),send(ir2,e_var(x7),sum_ty(unit,int),pair(0,e_tt))]),skip)]))]),[],Name) :-
    T = par([send(p0,e_pid(p1),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,pair(0,10))),while(p1,true,seq([recv(p1,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x11,pair(x13,x14))),ite(p1,x11 = 0,seq([nondet(x17,set(r2)),send(p1,e_pid(X17),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(0,x12))]),seq([nondet(X20,set(r2)),send(p1,e_pid(X20),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,x12))]))])),sym(IR2,set(r2),while(IR2,true,seq([recv(IR2,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x4,pair(x6,x7))),ite(IR2,x4 = 0,seq([seq([assign(IR2,e1,1),while(IR2,e1 = 1,seq([assign(IR2,e1,0),skip]))]),send(IR2,e_var(x7),sum_ty(unit,int),pair(0,e_tt))]),skip)])))]),
    Name = database-sample-newer.

 
rewrite_query(T,skip,[],Name) :-
    T = par([for(p0,XL0,set(r1),seq([recv(p0,type(pid),x3),send(p0,e_var(x3),pid,p0)])),for(p2,XL2,set(r1),seq([recv(p2,type(unit),x1)])),sym(IR1,set(r1),seq([send(IR1,e_pid(p0),pid,IR1),recv(IR1,type(pid),x2),send(IR1,e_pid(p2),unit,e_tt)]))]),
    Name = ping-multi-two-party.

rewrite_query(T,par([while(p1,true,seq([recv(p1,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x11,pair(x13,x14))),ite(p1,x11 = 0,seq([nondet(x17,set(r2)),send(p1,e_pid(x17),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(0,x12))]),seq([nondet(x20,set(r2)),send(p1,e_pid(x20),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,x12))]))])),while(ir2,true,seq([recv(ir2,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x4,pair(x6,x7))),ite(ir2,x4 = 0,seq([seq([assign(ir2,e1,1),while(ir2,e1 = 1,seq([assign(ir2,e1,0),skip]))]),send(ir2,e_var(x7),sum_ty(unit,int),pair(0,e_tt))]),skip)]))]),[],Name) :-
    T = par([send(p0,e_pid(p1),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,pair(0,10))),while(p1,true,seq([recv(p1,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x11,pair(x13,x14))),ite(p1,x11 = 0,seq([nondet(x17,set(r2)),send(p1,e_pid(X17),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(0,x12))]),seq([nondet(x20,set(r2)),send(p1,e_pid(X20),sum_ty(prod_ty(int,pid),prod_ty(int,int)),pair(1,x12))]))])),sym(IR2,set(r2),while(IR2,true,seq([recv(IR2,type(sum_ty(prod_ty(int,pid),prod_ty(int,int))),pair(x4,pair(x6,x7))),ite(IR2,x4 = 0,seq([seq([assign(IR2,e1,1),while(IR2,e1 = 1,seq([assign(IR2,e1,0),skip]))]),send(IR2,e_var(x7),sum_ty(unit,int),pair(0,e_tt))]),skip)])))]),
    Name = database-sample.

rewrite_query(T,skip,[],Name) :-
    T = par([seq([for(p0,XL0,set(r1),seq([send(p0,e_pid(XL0),pid,p0)])),for(p0,XL1,set(r1),seq([recv(p0,type(pid),x2)]))]),sym(IR1,set(r1),seq([recv(IR1,type(pid),x1),send(IR1,e_var(x1),pid,IR1)]))]),
    Name = ping-multi-size.

rewrite_query(T,par([
		     while(p0,true,seq([
					recv(p0,type(tapp(req,prod_ty(int,prod_ty(pid,int)))),pair(x16,pair(x18,x19))),ite(p0,0 = x16,assign(p0,x21,0),assign(p0,x21,1)),ite(p0,x21 = 0,ite(p0,ndet,seq([send(p0,e_var(x18),tapp(resp,sum_ty(unit,unit)),pair(0,e_tt)),recv(p0,e_var(x18),int,x24)]),send(p0,e_var(x18),tapp(resp,sum_ty(unit,unit)),pair(1,e_tt))),send(p0,e_var(x18),int,x25))]))]),[],Name) :-
	T = par([

		 while(p0,true,seq([
				    recv(p0,type(tapp(req,prod_ty(int,prod_ty(pid,int)))),pair(x16,pair(x18,x19))),ite(p0,0 = x16,assign(p0,x21,0),assign(p0,x21,1)),ite(p0,x21 = 0,ite(p0,ndet,seq([send(p0,e_var(x18),tapp(resp,sum_ty(unit,unit)),pair(0,e_tt)),recv(p0,e_var(x18),int,x24)]),send(p0,e_var(x18),tapp(resp,sum_ty(unit,unit)),pair(1,e_tt))),send(p0,e_var(x18),int,x25))])),sym(IR1,set(r1),seq([ite(IR1,ndet,assign(IR1,x3,0),assign(IR1,x3,1)),send(IR1,e_pid(p0),tapp(req,prod_ty(int,prod_ty(pid,int))),pair(x3,pair(IR1,3))),ite(IR1,0 = x3,assign(IR1,x6,0),assign(IR1,x6,1)),ite(IR1,x6 = 0,seq([recv(IR1,type(tapp(resp,sum_ty(unit,unit))),pair(x8,x9)),ite(IR1,x8 = 0,send(IR1,e_pid(p0),int,x10),skip)]),recv(IR1,type(int),x12))]))]),
    Name = bakst-concdb.
 
rewrite_query(T,skip,[],Name) :-
	T = par([seq([
		      recv(p0,type(prod_ty(int,prod_ty(pid,int))),pair(x10,pair(x12,x13))),
		      ite(p0,0 = x10,assign(p0,x15,0),assign(p0,x15,1)),
		      ite(p0,x15 = 0,send(p0,e_var(x12),unit,e_tt),die),
		      seq([assign(p0,e0,1),
			   while(p0,e0 = 1,
				 seq([assign(p0,e0,0),seq([recv(p0,type(prod_ty(int,prod_ty(pid,int))),pair(x21,pair(x23,x24))),ite(p0,0 = x21,assign(p0,x26,0),assign(p0,x26,1)),ite(p0,x26 = 0,die,seq([ite(p0,1 = x21,assign(p0,x29,0),assign(p0,x29,1)),ite(p0,x29 = 0,seq([send(p0,e_var(x23),int,0),assign(p0,e0,1)]),seq([ite(p0,2 = x21,assign(p0,x32,0),assign(p0,x32,1)),ite(p0,x32 = 0,assign(p0,e0,1),skip)]))]))])])
				)])
		     ]),seq([send(p1,e_pid(p0),prod_ty(int,prod_ty(pid,int)),pair(0,pair(p1,0))),recv(p1,type(unit),x2),send(p1,e_pid(p0),prod_ty(int,prod_ty(pid,int)),pair(2,pair(p1,0))),send(p1,e_pid(p0),prod_ty(int,prod_ty(pid,int)),pair(3,pair(p1,0)))])]),
    Name = bakst-parikh.


rewrite_query(T,skip,[],Name) :-
    T = par([seq([for(p0,XL0,set(r1),seq([send(p0,e_pid(XL0),int,4)])),for(p0,XL1,set(r1),seq([recv(p0,type(int),x5)]))]),sym(IR1,set(r1),seq([recv(IR1,type(int),x2),send(IR1,e_pid(p0),int,x2)]))]),
    Name = work-pushing.


rewrite_query(T,skip,[],Name) :-
    T = par([seq([iter(p0,x1,seq([recv(p0,type(pid),x7),send(p0,e_var(x7),sum_ty(int,unit),pair(0,XWQ0))])),for(p0,XWQ1,set(r1),seq([recv(p0,type(pid),x8),send(p0,e_var(x8),sum_ty(int,unit),pair(1,e_tt))]))]),iter(p2,x1,seq([recv(p2,type(int),x3)])),sym(IR1,set(r1),seq([assign(IR1,e0,1),while(IR1,e0 = 1,seq([assign(IR1,e0,0),seq([send(IR1,e_pid(p0),pid,IR1),recv(IR1,type(sum_ty(int,unit)),pair(x5,x6)),ite(IR1,x5 = 0,seq([send(IR1,e_pid(p2),int,x6),assign(IR1,e0,1)]),skip)])]))]))]),
    Name = map-reduce-bakst.

rewrite_query(T,skip,[],Name) :-
    T = par([seq([send(p0,e_pid(p1),tapp(mastermsg,pid),p0),for(p0,XL1,set(r2),seq([send(p0,e_pid(XL1),tapp(mastermsg,pid),p1)])),recv(p0,type(unit),x8)]),seq([recv(p1,type(tapp(mastermsg,pid)),x2),for(p1,XL2,set(r2),seq([recv(p1,type(tapp(clientmsg,pid)),x4)])),send(p1,e_var(x2),unit,e_tt)]),sym(IR2,set(r2),seq([recv(IR2,type(tapp(mastermsg,pid)),x6),send(IR2,e_var(x6),tapp(clientmsg,pid),IR2)]))]),
    Name=registry-bakst.

rewrite_query(T,skip,[],Name) :-
    T = par([for(p0,XL0,set(r1),seq([recv(p0,type(pid),x6),send(p0,e_var(x6),pid,p0)])),for(p2,XL2,set(r1),seq([recv(p2,type(unit),x2)])),sym(IR1,set(r1),seq([send(IR1,e_pid(p0),pid,IR1),recv(IR1,type(pid),x4),send(IR1,e_pid(p2),unit,e_tt)]))]),
    Name = ping-multi-bakst.

rewrite_query(T,skip,[],Name) :-
    T = par([seq([iter(p0,x1,seq([recv(p0,type(pid),x8),send(p0,e_var(x8),sum_ty(int,unit),pair(0,XWQ0))])),for(p0,XWQ1,set(r1),seq([recv(p0,type(pid),x10),send(p0,e_var(x10),sum_ty(int,unit),pair(1,e_tt))]))]),sym(IR1,set(r1),seq([assign(IR1,e0,1),while(IR1,e0 = 1,seq([assign(IR1,e0,0),seq([send(IR1,e_pid(p0),pid,IR1),recv(IR1,type(sum_ty(int,unit)),pair(x6,x4)),ite(IR1,x6 = 0,assign(IR1,e0,1),skip)])]))]))]),
    Name = work-stealing-bakst.

rewrite_query(T,skip,[],Name) :-
    T = par([seq([for(p0,XL0,set(r1),seq([send(p0,e_pid(XL0),pid,p0)])),for(p0,XL1,set(r1),seq([recv(p0,type(pid),x4)]))]),sym(IR1,set(r1),seq([recv(IR1,type(pid),x2),send(IR1,e_var(x2),pid,IR1)]))]),
    Name = ping-multi-bakst.

rewrite_query(T,skip,[],Name) :-
    T = par([skip,seq([recv(p1,type(tapp(forward,sum_ty(pid,pid))),pair(x3,x1)),ite(p1,x3 = 0,send(p1,e_var(x1),int,x4),die)]),seq([recv(p2,type(tapp(clientreq,sum_ty(pid,pid))),pair(x8,x6)),ite(p2,x8 = 0,seq([send(p2,e_pid(p1),tapp(forward,sum_ty(pid,pid)),pair(0,p2)),recv(p2,type(int),x11),send(p2,e_var(x6),tapp(fwint,int),x11)]),send(p2,e_var(x6),tapp(fwint,int),x12))]),seq([send(p3,e_pid(p2),tapp(clientreq,sum_ty(pid,pid)),pair(0,p3)),recv(p3,type(tapp(fwint,int)),x15)])]),
    Name = firewall-bakst.

rewrite_query(T,
	      par([
		   sym(IR1,set(r1),
		       while(IR1,true,
			     seq([
				  recv(IR1,type(pid),x1),
				  send(IR1,e_var(x1),pid,IR1)
				 ])
			    )
		      )
		  ]),
	      [],Name) :-
	T = par([
		 nondet(X4, set(r1),
			seq([
			     send(p0,e_pid(X4),pid,p0),
			     recv(p0,e_pid(X4),type(pid),x7)
			    ])
		       ),
		 sym(IR1, set(r1),
		     while(IR1,true,
			   seq([
				recv(IR1,type(pid),x1),
				send(IR1,e_var(x1),pid,IR1)
			       ])
			  )
		    )
		]),
	Name = nondet-sym.



rewrite_query(T,skip,[(p0,p2)],Name) :-
    T = par([seq([iter(p0,x1,seq([recv(p0,type(pid),x11),send(p0,e_var(x11),sum_ty(int,unit),pair(0,XWQ0))])),for(p0,XWQ1,set(r1),seq([recv(p0,type(pid),x13),send(p0,e_var(x13),sum_ty(int,unit),pair(1,e_tt))]))]),iter(p2,x1,seq([recv(p2,type(int),x4)])),sym(IR1,set(r1),seq([assign(IR1,e0,1),while(IR1,e0 = 1,seq([assign(IR1,e0,0),seq([send(IR1,e_pid(p0),pid,IR1),recv(IR1,type(sum_ty(int,unit)),pair(x9,x7)),ite(IR1,x9 = 0,seq([send(IR1,e_pid(p2),int,x7),assign(IR1,e0,1)]),skip)])]))]))]),
    Name = verify1.
 
rewrite_query(T,skip,[(p0,p2)],Name) :-
	T = par([
		 seq([
		      iter(p0,x1,
			   seq([
				recv(p0,x11),
				send(p0,e_var(x11),sum_ty(int,unit),pair(0,_))
			       ])
			  ),
		      for(p0,_,set(r1),
			  seq([
			       recv(p0,type(pid),x13),
			       send(p0,e_var(x13),sum_ty(int,unit),pair(1,e_tt))
			      ])
			 )
		     ]),
		 iter(p2,x1,
		      seq([
			   recv(p2,type(int),x4)
			  ])
		     ),
		 sym(IR1,set(r1),
		     seq([
			  assign(IR1,e0,1),
			  while(IR1,e0 = 1,
				seq([
				     assign(IR1,e0,0),
				     seq([
					  send(IR1,e_pid(p0),pid,IR1),
					  recv(IR1,type(sum_ty(int,unit)),pair(x9,x7)),
					  ite(IR1,x9=0,seq([send(IR1,e_pid(p2),int,x7),assign(IR1,e0,1)]),skip)
					 ])
				    ])
			       )])
		    )]
	       ),
	Name = verify.



rewrite_query(T,skip,[],Name) :-
	S=
	seq([
	     assign(p0,e0,1),
	     while(p0,
		   e0=1,
		   seq([
			assign(p0,e0,0),
			seq([
			     recv(p0,x24),
			     ite(p0, x24=0,die,skip)
			    ])
		       ])
		  )
	    ]),
	W=send(p1,e_pid(p0),2),
	T=par([S,W]),
	Name=itebug.

rewrite_query(T,skip,[(p0,p2)],Name) :-
	T = par([
		 seq([
		      iter(p0,x1,
			   seq([
				recv(p0,type(pid),x11),
				send(p0,e_var(x11),sum_ty(int,unit),pair(0,XWQ0))
			       ])),
		      for(p0,XWQ1,set(r1),
			  seq([
			       recv(p0,type(pid),x13),
			       send(p0,e_var(x13),sum_ty(int,unit),pair(1,e_tt))
			      ])
			 )
		     ]),
		 iter(p2,x1,seq([
				 recv(p2,type(int),x4)
				])
		     ),
		 sym(IR1,set(r1),seq([
				      assign(IR1,e0,1),
				      while(IR1,e0 = 1,
					    seq([
						 assign(IR1,e0,0),
						 seq([
						      send(IR1,e_pid(p0),pid,IR1),
						      recv(IR1,type(sum_ty(int,unit)),pair(x9,x7)),
						      ite(IR1,x9 = 0,
							  seq([
							       send(IR1,e_pid(p2),int,x7),
							       assign(IR1,e0,1)
							      ]),
							  skip
							 )
						     ])
						])
					   )
				     ])
		    )
		]),
    Name = bakst-map-reduce.

rewrite_query(T,skip,[],Name) :-
    T = par([seq([assign(p0,e0,1),while(p0,e0=1,assign(p0,e0,0))]),skip]),
    Name = verify-bug.

rewrite_query(T,skip,[],Name) :-
	T = par([
		 seq([
		      recv(p0,type(prod_ty(int,prod_ty(pid,int))),pair(x8,pair(x10,x11))),
		      ite(p0,0 = x8,assign(p0,x13,0),assign(p0,x13,1)),
		      ite(p0,x13=0,
			  seq([
			       send(p0,e_var(x10),unit,e_tt),
			       seq([
				    assign(p0,e0,1),
				    while(p0,
					  e0=1,
					  seq([
					       assign(p0,e0,0),
					       seq([
						    recv(p0,type(prod_ty(int,prod_ty(pid,int))),pair(x19,pair(x21,x22))),
						    ite(p0,0 = x19,assign(p0,x24,0),assign(p0,x24,1)),
						    ite(p0,x24 = 0,die,skip)
						   ])
					      ])
					 )
				   ])
			      ]),
			  die)
		     ]),
		 seq([
		      send(p1,e_pid(p0),prod_ty(int,prod_ty(pid,int)),pair(0,pair(p1,0))),
		      recv(p1,type(unit),x2),
		      send(p1,e_pid(p0),prod_ty(int,prod_ty(pid,int)),pair(2,pair(p1,3)))
		     ])
		]),
    Name = verify1.