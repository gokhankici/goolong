rewrite_query(par([seq([assign(a, loop1, 1), Server]),Client]),Server,[], client-master) :-
	Server=
	while(a,loop1=1,
		     seq([
			  assign(a, loop1, 0), 
			  recv(a, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI))), ds_deMH),
			  cases(a,
				ds_deMH,
				[
				 case(a,
				      cstr__Tuple(who, msg),
				      seq([
				     cases(a,
					   msg,
					   [
					    case(a,
						 cstr__GetTag(tid),
						 seq([
						      assign(a, t0, cstr__Nothing(null___)),
						      cases(a,
							    res,
							    [
							     case(a, cstr__Nothing(null___), assign(a, anf3, cstr__Nil(null___))), 
							     case(a, cstr__Just(a), assign(a, anf3, ndet))
							    ], skip
							   ), 
						      assign(a, dll__dll__brisk_anf_dyoc, anf3), 
						      assign(a, anf5, cstr__TagRefs(dll__dll__brisk_anf_dyoc)), 
						      assign(a, anf4, cstr__ReplyMsg(anf5, st0)), 
						      assign(a, reply, anf4)
						     ])
						)
					   ], skip),
					   cases(a,
						 reply,
						 [
						  case(a,
						       cstr__ReplyMsg(r, s_),
						       seq([
							    assign(a, anf7, cstr__SelfSigned(a, r)), 
							    send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf7)
							   ])
						      ), 
						  case(a, cstr__NoReply(s_), skip)
						 ],
						 skip)
					  ])
				     )
				],
				skip
			       ),
			  assign(a, st0, s_), 
			  assign(a, loop1, 1)
			 ])
		    ),
	Client=sym(B, b_Set,
		   seq([
			assign(B, anf2, cstr__TagId(ndet)), 
			assign(B, anf1, cstr__GetTag(anf2)), 
			assign(B, anf0, cstr__Tuple(B, anf1)), 
			send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf0), 
		        recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg),
			cases(B, msg, [
				       case(B, cstr__SelfSigned(x, pay), assign(B, bla, pay))
				      ], skip
			     )
		       ])
		  ).
	
rewrite_query(par([Master,TagServer]),sym(C, c_Set,WhileTag),[], master-server) :-
	Master=seq([
		    assign(a, t0, cstr__Nothing(null___)), 
		    for(a, Tn,
			c_Set,
			seq([
			     assign(a, tn, Tn), 
			     assign(a, anf2, cstr__GetTag(tid)), 
			     assign(a, anf1, cstr__Tuple(a, anf2)), 
			     send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf1), 
			     recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_) ,
			     cases(a, msg_,
				   [
				    case(a, cstr__SelfSigned(X, pay), assign(a, t, pay))
				   ], skip)
			    ])
		       ),
		    cases(a,
			  res,
			  [
			   case(a, cstr__Nothing(null___), assign(a, anf3, cstr__Nil(null___))), 
			   case(a, cstr__Just(a), assign(a, anf3, ndet))
			  ],
			  skip
			 ), 
		    assign(a, dll__dll__brisk_anf_dyoc, anf3), 
		    assign(a, anf5, cstr__TagRefs(dll__dll__brisk_anf_dyoc)), 
		    assign(a, anf4, cstr__ReplyMsg(anf5, st0)), 
		    assign(a, reply, anf4)
		   ]),
	TagServer=sym(C, c_Set,
		      seq([
			   assign(C, dll__dll__brisk_anf_drsV, ndet), 
			   assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drsV)), 
			   assign(C, st0, anf0), 
			   seq([
				assign(C, loop0, 1), 
				WhileTag
			       ])
			  ])
		     ),
		WhileTag=while(C, loop0=1,
			       seq([
				    assign(C, loop0, 0), 
				    recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deMH),
				    cases(C,
					  ds_deMH,
					  [
					   case(C,
						cstr__Tuple(who, msg),
						seq([
						     cases(C,
							   msg, [
								 case(C,
								      cstr__GetTag(tid),
								      seq([
									   assign(C, dll__dll__brisk_anf_drsO, ndet), 
									   cases(C,
										 dll__dll__brisk_anf_drsO,
										 [
										  case(C, cstr__Nothing(null___),
										       assign(C, anf1, cstr__TagNotFound(null___))
										      ), 
										  case(C, cstr__Just(a),
										       assign(C, anf1, cstr__TagFound(a))
										      )
										 ], skip
										), 
									   assign(C, dll__dll__brisk_anf_drsP, anf1), 
									   assign(C, anf2, cstr__ReplyMsg(dll__dll__brisk_anf_drsP, st0)), 
									   assign(C, reply, anf2)])
								     ) ,
								 case(C, cstr__GetTagInfo(tid),
								      seq([
									   assign(C, anf3, cstr__ReplyMsg(cstr__OK(null___), st0)), 
									   assign(C, reply, anf3)])
								     ), 
								 case(C,
								      cstr__SetTag(tid, t),
								      seq([
									   assign(C, anf4, cstr__ReplyMsg(cstr__OK(null___), st0)), 
									   assign(C, reply, anf4)
									  ])
								     )
								], skip),
								cases(C, reply, [
										 case(C, cstr__ReplyMsg(r, s_),
										      seq([
											   assign(C, anf5, cstr__SelfSigned(C, r)), 
											   send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf5)
										])
									   ), 
										 case(C, cstr__NoReply(s_), skip)
										],skip
							  )
						    ])
					       )], skip), 
				    assign(C, st0, s_), 
				    assign(C, loop0, 1)
				   ])
			      ).
	

rewrite_query(T,Rem,[], tagnode_1st) :-
	Rem=par([WhileM,sym(C, c_Set,WhileTag)]),
	T=par([Master,Client,TagServer]), 
	WhileM=while(a,
		     loop1=1,
		     seq([
			  assign(a, loop1, 0), 
			  recv(a, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI))), ds_deMH), 
			  cases(a,
				ds_deMH,
				[
				 case(a,
				      cstr__Tuple(who, msg),
				      seq([
					   cases(a,
						 msg,
						 [
						  case(a,
						       cstr__GetTag(tid),
						       seq([
							    assign(a, t0, cstr__Nothing(null___)) ,
							    
							    for(a, Tn,
								c_Set,
								seq([
								     assign(a, tn, Tn), 
								     assign(a, anf2, cstr__GetTag(tid)), 
								     assign(a, anf1, cstr__Tuple(a, anf2)), 
								     send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf1), 
								     recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
								     cases(a, msg_,
									   [
									    case(a, cstr__SelfSigned(X, pay), assign(a, t, pay))
									   ], skip)
								    ])
							       ),
							    cases(a,
								  res,
								  [
								   case(a, cstr__Nothing(null___), assign(a, anf3, cstr__Nil(null___))), 
								   case(a, cstr__Just(a), assign(a, anf3, ndet))
								  ],
								  skip
								 ), 
							    assign(a, dll__dll__brisk_anf_dyoc, anf3), 
							    assign(a, anf5, cstr__TagRefs(dll__dll__brisk_anf_dyoc)), 
							    assign(a, anf4, cstr__ReplyMsg(anf5, st0)), 
							    assign(a, reply, anf4)
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
							    assign(a, anf7, cstr__SelfSigned(a, r)), 
							    send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf7)
							   ])
						      ), 
						  case(a, cstr__NoReply(s_), skip)
						 ],
						 skip)
					  ])
				     )
				],
				skip
			       ), 
			  assign(a, st0, s_), 
			 assign(a, loop1, 1)
			])
		    ),

	Master=seq([
		    cases(a,
			  cstr__MS(ndet, ndet, 0),
			  [
			   case(a, cstr__MS(ds_dycn, ds_dyco, ds_dycp), assign(a, anf0, cstr__MS(ndet, c_Set, ds_dycp)))
			  ],
			  skip
			 ), 
		    assign(a, dll__dll__brisk_anf_dyng, anf0), 
		    assign(a, st0, dll__dll__brisk_anf_dyng), 
		    seq([ assign(a, loop1, 1), WhileM])
		   ]),      
	TagServer=sym(C, c_Set,
		      seq([
			   assign(C, dll__dll__brisk_anf_drsV, ndet), 
			   assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drsV)), 
			   assign(C, st0, anf0), 
			   seq([
				assign(C, loop0, 1), 
				WhileTag
			       ])
			  ])
		   ),
	Client=sym(B, b_Set,
		   seq([
			assign(B, anf2, cstr__TagId(ndet)), 
			assign(B, anf1, cstr__GetTag(anf2)), 
			assign(B, anf0, cstr__Tuple(B, anf1)), 
			send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf0), 
			recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg), 
			cases(B, msg, [
				       case(B, cstr__SelfSigned(x, pay), assign(B, bla, pay))
				      ], skip)
			])
		  ),
	WhileTag=while(C, loop0=1,
	      seq([
		   assign(C, loop0, 0), 
		   recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deMH), 
		   cases(C,
			 ds_deMH,
			 [
			  case(C,
			       cstr__Tuple(who, msg),
			       seq([
				    cases(C,
					  msg, [
						case(C,
						     cstr__GetTag(tid),
						     seq([
							  assign(C, dll__dll__brisk_anf_drsO, ndet), 
							  cases(C,
								dll__dll__brisk_anf_drsO,
								[
								 case(C, cstr__Nothing(null___),
								      assign(C, anf1, cstr__TagNotFound(null___))
								     ), 
								 case(C, cstr__Just(a),
								      assign(C, anf1, cstr__TagFound(a))
								     )
								], skip
							       ), 
							  assign(C, dll__dll__brisk_anf_drsP, anf1), 
							  assign(C, anf2, cstr__ReplyMsg(dll__dll__brisk_anf_drsP, st0)), 
							  assign(C, reply, anf2)])), 
						case(C, cstr__GetTagInfo(tid),
						     seq([
							  assign(C, anf3, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							  assign(C, reply, anf3)])
									    ), 
						case(C,
						     cstr__SetTag(tid, t),
						     seq([
							  assign(C, anf4, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							  assign(C, reply, anf4)
							 ])
						    )
					       ], skip), 
				    cases(C, reply, [ case(C, cstr__ReplyMsg(r, s_),
							   seq([
								assign(C, anf5, cstr__SelfSigned(C, r)), 
								send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf5)
							       ])
							  ), 
						      case(C, cstr__NoReply(s_), skip)],
					  skip)
				   ])
			      )], skip), 
		   assign(C, st0, s_), 
		   assign(C, loop0, 1)
		  ])
		      ).

% proctype a:
%   anf0 := case (MS({@SymSet[ProcessId]},{@SymSet[ProcessId]},0)) of
%             MS ds_dyee ds_dyef ds_dyeg ->
%               (MS({@SymSet[ProcessId]},%c_Set,ds_dyeg))
%   $$brisk_anf_dyp7 := anf0
%   st0 := $$brisk_anf_dyp7
%   while true:
%     ds_deNr := recv[Tuple[ProcessId MasterAPI]]
%     match ds_deNr:
%       case (Tuple(who,msg)):
%         match msg:
%           case (AddBlob(ds_dydO,ds_dydP)):
%             anf1 := (ReplyMsg(OK,st0))
%             reply := anf1
%           case (GetTag(tid)):
%             anf2 := (ReplyMsg(OK,st0))
%             reply := anf2
%           case (AddTag(tag,refs)):
%             best := Nothing
%             for tn in %c_Set:
%               anf4 := (GetTag(tag))
%               anf3 := (Tuple(%a,anf4))
%               send[Tuple[ProcessId TagNodeAPI]](tn,anf3)
%               msg' := recvFrom[SelfSigned[TagNodeResponse]](tn)
%               match msg':
%                 case (SelfSigned(X,pay)):
%                   tag' := pay
%               $$brisk_anf_dyoO := {@Maybe Int}
%               match $$brisk_anf_dyoO:
%                 case Nothing:
%                   match tag':
%                     case (TagFound(t)):
%                       match t:
%                         case (Tag(ds_dyds,ds_dydt,ds_dydu)):
%                           anf5 := (Just({@Tag}))
%                           best := anf5
%                     __DEFAULT__:
%                       skip
%                 case (Just(i)):
%                   match tag':
%                     case (TagFound(t)):
%                       match t:
%                         case (Tag(ds_dydp,ds_dydq,ds_dydr)):
%                           $$brisk_anf_dyoS := {@Bool}
%                           match $$brisk_anf_dyoS:
%                             case False:
%                               match tag':
%                                 case (TagFound(t)):
%                                   match t:
%                                     case (Tag(ds_dyds,ds_dydt,ds_dydu)):
%                                       anf6 := (Just({@Tag}))
%                                       best := anf6
%                                 __DEFAULT__:
%                                   skip
%                             case True:
%                               anf7 := (Just({@Tag}))
%                               best := anf7
%                     __DEFAULT__:
%                       match tag':
%                         case (TagFound(t)):
%                           match t:
%                             case (Tag(ds_dyds,ds_dydt,ds_dydu)):
%                               skip
%                         __DEFAULT__:
%                           skip
%             anf8 := case best of
%                       Nothing ->
%                         (Tag(tag,refs,0))
%                       Just a ->
%                         case %a of
%                           Tag ds_dycr ds_dycs ds_dyct ->
%                             (Tag(ds_dycr,{@List[TagRef]},{@Int}))
%             $$brisk_anf_dyoZ := anf8
%             ds_dycB := Unit
%             for tn in %c_Set:
%               anf10 := (SetTag(tag,$$brisk_anf_dyoZ))
%               anf9 := (Tuple(%a,anf10))
%               send[Tuple[ProcessId TagNodeAPI]](tn,anf9)
%               msg' := recvFrom[SelfSigned[TagNodeResponse]](tn)
%               match msg':
%                 case (SelfSigned(X,pay)):
%                   _ := pay
%             anf11 := (ReplyMsg(OK,st0))
%             reply := anf11
%         match reply:
%           case (ReplyMsg(r,s')):
%             anf12 := (SelfSigned(%a,r))
%             send[SelfSigned[MasterResponse]](who,anf12)
%           case (NoReply(s')):
%             skip
%     st0 := s'
%     continue
% proctype (C:c_Set):
%   $$brisk_anf_drth := {@HashMap[TagId Tag]}
%   anf0 := (TagState($$brisk_anf_drth))
%   st0 := anf0
%   while true:
%     ds_deNr := recv[Tuple[ProcessId TagNodeAPI]]
%     match ds_deNr:
%       case (Tuple(who,msg)):
%         match msg:
%           case (GetTag(tid)):
%             $$brisk_anf_drt9 := {@Maybe[Tag]}
%             anf1 := case $$brisk_anf_drt9 of
%                       Nothing ->
%                         TagNotFound
%                       Just a ->
%                         (TagFound(%a))
%             $$brisk_anf_drta := anf1
%             anf2 := (ReplyMsg($$brisk_anf_drta,st0))
%             reply := anf2
%           case (GetTagInfo(tid)):
%             anf3 := (ReplyMsg(OK,st0))
%             reply := anf3
%           case (SetTag(tid,tag)):
%             anf4 := case st0 of
%                       TagState ds_drm7 ->
%                         (TagState({@HashMap[TagId Tag]}))
%             $$brisk_anf_drtb := anf4
%             anf5 := (ReplyMsg(OK,$$brisk_anf_drtb))
%             reply := anf5
%         match reply:
%           case (ReplyMsg(r,s')):
%             anf6 := (SelfSigned(C,r))
%             send[SelfSigned[TagNodeResponse]](who,anf6)
%           case (NoReply(s')):
%             skip
%     st0 := s'
%     continue
% proctype (B:b_Set):
%   anf2 := (TagId({@Process String}))
%   anf1 := (GetTag(anf2))
%   anf0 := (Tuple(B,anf1))
%   send[Tuple[ProcessId MasterAPI]](%a,anf0)
%   msg := recvFrom[SelfSigned[MasterResponse]](%a)
%   match msg:
%     case (SelfSigned(X,pay)):
%       _ := pay
rewrite_query(T, Rem, [], tagnode_2nd) :-
	%Rem=par([sym(C, c_Set, WhileTagServer), WhileMaster]),
	Rem=par([WhileMaster,sym(C, c_Set, WhileTagServer)]),
	%T=par([Master,Client,TagServer]),
	T=par([Client,Master,TagServer]),					 
	Master=
	seq([
	     cases(a,
		   cstr__MS(ndet, ndet, 0), [
					     case(a,
						  cstr__MS(ds_dyee, ds_dyef, ds_dyeg),
						  assign(a, anf0, cstr__MS(ndet, c_Set, ds_dyeg))
						 )
					    ],
		   skip
		  ),
	     assign(a, dll__dll__brisk_anf_dyp7, anf0), 
	     assign(a, st0, dll__dll__brisk_anf_dyp7),
	     seq([
		  assign(a, loop1, 1), 
		  WhileMaster
		 ])
	    ]),
	MasterForLoop1=
	for(a, Tn,
	    c_Set,
	    seq([
		 assign(a, tn, Tn), 
		 assign(a, anf4, cstr__GetTag(tag)), 
		 assign(a, anf3, cstr__Tuple(a, anf4)), 
		 send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf3), 
		 recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
		 cases(a,
		       msg_,
		       [
			case(a, cstr__SelfSigned(X, pay), assign(a, tag_, pay))
		       ],
		       skip
		      ), 
		 assign(a, dll__dll__brisk_anf_dyoO, ndet), 
		 cases(a,
		       dll__dll__brisk_anf_dyoO,
		       [
			case(a,
			     cstr__Nothing(null___),
			     cases(a, tag_,
				   [
				    case(a,
					 cstr__TagFound(t),
					 cases(a,
					       t,
					       [
						case(a,
						     cstr__Tag(ds_dyds, ds_dydt, ds_dydu),
						     seq([
							  assign(a, anf5, cstr__Just(ndet)), 
							  assign(a, best, anf5)
							 ])
						    )
					       ],
					       skip)
					)
				   ],
				   skip
				  )
			    ), 
			case(a,
			     cstr__Just(i),
			     cases(a,
				   tag_,
				   [
				    case(a,
					 cstr__TagFound(t),
					 cases(a,
					       t,
					       [
						case(a,
						     cstr__Tag(ds_dydp, ds_dydq, ds_dydr),
						     seq([
							  assign(a, dll__dll__brisk_anf_dyoS, ndet), 
							  cases(a,
								dll__dll__brisk_anf_dyoS,
								[
								 case(a,
								      cstr__False(null___),
								      cases(a,
									    tag_,
									    [
									     case(a,
										  cstr__TagFound(t),
										  cases(a,
											t,
											[
											 case(a,
											      cstr__Tag(ds_dyds, ds_dydt, ds_dydu),
											      seq([
												   assign(a, anf6, cstr__Just(ndet)), 
												   assign(a, best, anf6)
												  ])
											     )
											]
										       , skip)
										 )
									    ], skip)
								     ), 
								 case(a,
								      cstr__True(null___),
								      seq([
									   assign(a, anf7, cstr__Just(ndet)), 
									   assign(a, best, anf7)
									  ])
								     )
								],
								skip
							       )
							 ])
						    )
					       ],
					       skip)
					)
				   ],
				   skip
				  /*
				  default(a,
					  cases(a,
						tag_,
						[
						 case(a,
						      cstr__TagFound(t),
						      cases(a,
							    t,
							    [
							     case(a, cstr__Tag(ds_dyds, ds_dydt, ds_dydu),
								  skip
								 )
							    ],
							    skip)
						     )
						], skip))
				  */
				  )
			    )
		       ],
		       skip
		      )
		])
	   ),
	WhileMaster=
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
						     cstr__AddBlob(ds_dydO, ds_dydP),
						     seq([
							  assign(a, anf1, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							  assign(a, reply, anf1)
							 ])
						    ), 
						case(a,
						     cstr__GetTag(tid),
						     seq([
							  assign(a, anf2, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							  assign(a, reply, anf2)
							 ])
						    ), 
						case(a,
						     cstr__AddTag(tag, refs),
						     seq([
							  assign(a, best, cstr__Nothing(null___)), 
							  MasterForLoop1,
							  cases(a,
								best,
								[
								 case(a, cstr__Nothing(null___),
								      assign(a, anf8, cstr__Tag(tag, refs, 0))), 
								 case(a,
								      cstr__Just(a),
								      assign(a,
									     anf8,
									     bshit
									     /*
									     cases(a,
										   a,
										   [
										    case(a,
											 cstr__Tag(ds_dycr, ds_dycs, ds_dyct),
											 cstr__Tag(ds_dycr, ndet, ndet)
											)
										   ],
										   skip)
									    */
									    )
								     )
								],
								skip
							       ), 
							  assign(a, dll__dll__brisk_anf_dyoZ, anf8), 
							  assign(a, ds_dycB, cstr__Unit(null___)),
							  for(a, Tn,
							      c_Set,
							      seq([
								   assign(a, tn, Tn), 
								   assign(a, anf10, cstr__SetTag(tag, dll__dll__brisk_anf_dyoZ)), 
								   assign(a, anf9, cstr__Tuple(a, anf10)), 
								   send(a,
									e_var(tn),
									tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)),
									anf9
								       ), 
								   recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
								   cases(a,
									 msg_,
									 [
									  case(a, cstr__SelfSigned(X, pay), assign(a, null, pay))
									 ],
									 skip
									)
								  ]
								 )
							     ),
							  assign(a, anf11, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							  assign(a, reply, anf11)])
						    )],
					       skip
					      ), 
					 cases(a,
					       reply,
					       [
						case(a,
						     cstr__ReplyMsg(r, s_),
						     seq([
							  assign(a, anf12, cstr__SelfSigned(a, r)), 
							  send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf12)
							 ])
						    ), 
						case(a, cstr__NoReply(s_), skip)
					       ], skip)
					])
				   )
			      ],
			      skip
			     ), 
			assign(a, st0, s_), 
			assign(a, loop1, 1)
		       ])
		  ),
	     WhileTagServer=
	while(C,
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
				    %send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf6),
				    cases(C, msg,
					  [
					   case(C,
						cstr__GetTag(tid),
						seq([
						     assign(C, dll__dll__brisk_anf_drt9, ndet), 
						     cases(C,
							   dll__dll__brisk_anf_drt9,
							   [
							    case(C, cstr__Nothing(null___), assign(C, anf1, cstr__TagNotFound(null___))), 
							    case(C, cstr__Just(a), assign(C, anf1, cstr__TagFound(a)))
							   ],
							   skip
							  ), 
						     assign(C, dll__dll__brisk_anf_drta, anf1), 
						     assign(C, anf2, cstr__ReplyMsg(dll__dll__brisk_anf_drta, st0)), 
						     assign(C, reply, anf2)
						    ])
					       ), 
					   case(C,
						cstr__GetTagInfo(tid),
						seq([
						     assign(C, anf3, cstr__ReplyMsg(cstr__OK(null___), st0)), 
						     assign(C, reply, anf3)])), 
					   case(C,
						cstr__SetTag(tid, tag),
						seq([
						     cases(C,
							   st0,
							   [
							    case(C, cstr__TagState(ds_drm7), assign(C, anf4, cstr__TagState(ndet)))
							   ],
							   skip
							  ), 
						     assign(C, dll__dll__brisk_anf_drtb, anf4), 
						     assign(C, anf5, cstr__ReplyMsg(cstr__OK(null___), dll__dll__brisk_anf_drtb)), 
						     assign(C, reply, anf5)]))], skip), 
				    cases(C,
					  reply,
					  [
					   case(C,
						cstr__ReplyMsg(r, s_),
						seq([
						     assign(C, anf6, cstr__SelfSigned(C, r)), 
						     send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf6)
						    ])
					       ), 
					   case(C,
						cstr__NoReply(s_),
						skip
					       )
					  ],
					  skip
					 )
				   ])
			      )
			 ],
			 skip
			), 
		   assign(C, st0, s_), 
		   assign(C, loop0, 1)
		  ])
	     ),
	TagServer=
	sym(C, c_Set,
	    seq([
		 assign(C, dll__dll__brisk_anf_drth, ndet), 
		 assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drth)), 
		 assign(C, st0, anf0), 
		 seq([
		      assign(C, loop0, 1),
		      WhileTagServer
		     ])
		])
	   ),
	Client=sym(B, b_Set,
		   seq([
			assign(B, anf2, cstr__TagId(ndet)), 
			assign(B, anf1, cstr__AddTag(anf2, ndet)), 
			assign(B, anf0, cstr__Tuple(B, anf1)),
			send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf0), 
			recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg) ,
			cases(B,
			      msg, [
				       case(B, cstr__SelfSigned(X, pay), assign(B, null, pay))
				      ],
			      skip
			     )
		       ])
		  ).


rewrite_query(T,Rem,[],tagnode2-bakst) :-
	Rem=par([While,sym(C,c_Set,SymWhile)]),
	While=
	while(a, loop1=1,
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
						cstr__AddBlob(ds_dydr, ds_dyds),
						seq([
						     assign(a, anf1, cstr__ReplyMsg(cstr__OK(null___), st0)), 
						     assign(a, reply, anf1)
						    ])
					       ), 
					   case(a,
						cstr__GetTag(tid),
						seq([
						     assign(a, anf2, cstr__ReplyMsg(cstr__OK(null___), st0)), 
						     assign(a, reply, anf2)
						    ])
					       ), 
					   case(a, cstr__AddTag(tag, refs),
						seq([
						     assign(a, best, cstr__Nothing(null___)), 
						     for(a,
							 Tn,
							 c_Set,
							 seq([
							      assign(a, tn, Tn), 
							      assign(a, anf4, cstr__GetTag(tag)), 
							      assign(a, anf3, cstr__Tuple(a, anf4)), 
							      send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf3), 
							      recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
							      cases(a, msg_, [
									      case(a, cstr__SelfSigned(X, pay), assign(a, tag_, pay))
									     ],
								    skip
								   ), 
							      cases(a,
								    tag_,
								    [
								     case(a, cstr__OK(null___), skip), 
								     case(a, cstr__TagInfo(i), skip), 
								     case(a,
									  cstr__TagFound(t),
									  cases(a,
										t,
										[
										 case(a,
										      cstr__Tag(ds_dyd9, ds_dyda, ds_dydb),
										      seq([
											   assign(a, dll__dll__brisk_anf_dyoq, ndet), 
											   cases(a,
												 dll__dll__brisk_anf_dyoq,
												 [
												  case(a,
												       cstr__Nothing(null___),
												       seq([
													    assign(a, anf5, cstr__Just(ndet)), 
													    assign(a, best, anf5)])), 
												  case(a,
												       cstr__Just(i),
												       seq([
													    assign(a, dll__dll__brisk_anf_dyot, ndet), 
													    cases(a,
														  dll__dll__brisk_anf_dyot,
														  [
														   case(a, cstr__False(null___), skip), 
														   case(a, cstr__True(null___),
															seq([
															     assign(a, anf6, cstr__Just(ndet)), 
															     assign(a, best, anf6)
															    ])
														       )
														  ]
														 ,
														  skip
														 )
													   ])
												      )
												 ], skip
												)
											  ])
										     )
										], skip
									       )
									 ), 
								     case(a,
									  cstr__TagNotFound(null___),
									  skip
									 )
								    ], skip
								   )
							     ])
							), 
						     cases(a, best,
							   [
							    case(a, cstr__Nothing(null___), assign(a, anf7, cstr__Tag(tag, refs, 0))), 
							    case(a,
								 cstr__Just(a),
								 assign(a, anf7,
									cases(a, a,
									      [
									       case(a, cstr__Tag(ds_dycA, ds_dycB, ds_dycC), cstr__Tag(ds_dycA, ndet, ndet))
									      ], skip
									     )
								       )
								)
							   ], skip
							  ), 
						     assign(a, dll__dll__brisk_anf_dyoA, anf7), 
						     assign(a, ds_dycK, cstr__Unit(null___)),
						     for(a,
							 Tn,
							 c_Set,
							 seq([
							      assign(a, tn, Tn), 
							      assign(a, anf9, cstr__SetTag(tag, dll__dll__brisk_anf_dyoA)), 
							      assign(a, anf8, cstr__Tuple(a, anf9)), 
							      send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf8), 
							      recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
							      cases(a,
								    msg_,
								    [
								     case(a, cstr__SelfSigned(X, pay), assign(a, null, pay))
								    ],
								    skip
								   )
							     ])
							),
						     assign(a, anf10, cstr__ReplyMsg(cstr__OK(null___), st0)), 
						     assign(a, reply, anf10)]))], skip), 
				    cases(a,
					  reply,
					  [
					   case(a,
						cstr__ReplyMsg(r, s_),
						seq([
						     assign(a, anf11, cstr__SelfSigned(a, r)), 
						     send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf11)])), 
					   case(a, cstr__NoReply(s_),
						skip
					       )
					  ], skip
					 )
				   ])
			      )
			 ], skip
			), 
		   assign(a, st0, s_), 
		   assign(a, loop1, 1)
		  ])
	     ),
	SymWhile=while(C, loop0=1,
		       seq([
			    assign(C, loop0, 0), 
			    recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deNr), 
			    cases(C,
				  ds_deNr,
				  [
				   case(C,
					cstr__Tuple(who, msg),
					seq([
					     cases(C,
						   msg,
						   [
						    case(C,
							 cstr__GetTag(tid),
							 seq([
							      assign(C, dll__dll__brisk_anf_drt9, ndet), 
							      cases(C,
								    dll__dll__brisk_anf_drt9,
								    [
								     case(C,
									  cstr__Nothing(null___),
									  assign(C, anf1, cstr__TagNotFound(null___))
									 ), 
								     case(C,
									  cstr__Just(a),
									  assign(C, anf1, cstr__TagFound(a))
									 )
								    ], skip
								   ), 
							      assign(C, dll__dll__brisk_anf_drta, anf1), 
							      assign(C, anf2, cstr__ReplyMsg(dll__dll__brisk_anf_drta, st0)), 
							      assign(C, reply, anf2)])), 
						    case(C,
							 cstr__GetTagInfo(tid),
							 seq([
							      assign(C, anf3, cstr__ReplyMsg(cstr__OK(null___), st0)), 
							      assign(C, reply, anf3)
							     ])
							), 
						    case(C,
							 cstr__SetTag(tid, tag),
							 seq([
							      cases(C, st0,
								    [
								     case(C,
									  cstr__TagState(ds_drm7),
									  assign(C, anf4, cstr__TagState(ndet))
									 )
								    ],
								    skip
								   ), 
							      assign(C, dll__dll__brisk_anf_drtb, anf4), 
							      assign(C, anf5, cstr__ReplyMsg(cstr__OK(null___), dll__dll__brisk_anf_drtb)), 
							      assign(C, reply, anf5)]))], skip), 
					     cases(C,
						   reply,
						   [
						    case(C,
							 cstr__ReplyMsg(r, s_),
							 seq([
							      assign(C, anf6, cstr__SelfSigned(C, r)), 
							      send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf6)
							     ])
							), 
						    case(C,
							 cstr__NoReply(s_),
							 skip
							)
						   ], skip)
					    ])
				       )],
				  skip
				 ), 
			    assign(C, st0, s_), 
			    assign(C, loop0, 1)])),
	T=par([ seq([ cases(a, cstr__MS(ndet, ndet, 0), [ case(a, cstr__MS(ds_dydR, ds_dydS, ds_dydT), assign(a, anf0, cstr__MS(ndet, c_Set, ds_dydT)))], skip), 
		      assign(a, dll__dll__brisk_anf_dyoI, anf0), 
		      assign(a, st0, dll__dll__brisk_anf_dyoI), 
		      seq([ assign(a, loop1, 1), While ]) ]), 
		sym(C, c_Set, seq([ assign(C, dll__dll__brisk_anf_drth, ndet), 
				    assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drth)), 
				    assign(C, st0, anf0), 
				    seq([ assign(C, loop0, 1), SymWhile])])), 
		sym(B, b_Set, seq([ assign(B, anf2, cstr__TagId(ndet)), 
				    assign(B, anf1, cstr__AddTag(anf2, ndet)), 
				    assign(B, anf0, cstr__Tuple(B, anf1)), 
				    send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf0), 
				    recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg), 
				    cases(B, msg, [ case(B, cstr__SelfSigned(X, pay), assign(B, null, pay))], skip)]))
	      ]).


rewrite_query(T,Rem,[],bast-cex) :- 
  While=while(a, loop1=1, seq([ assign(a, loop1, 0), 
                              recv(a, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI))), ds_deNr), 
                              cases(a, ds_deNr, [ case(a, cstr__Tuple(who, msg), seq([ cases(a, msg, [ case(a, cstr__AddBlob(ds_dy8D, ds_dy8E), seq([ assign(a, anf1, cstr__ReplyMsg(cstr__OK(null___), st0)), 
                                                                                                                                                      assign(a, reply, anf1)])), 
                                                                                                       case(a, cstr__GetTag(tid), seq([ assign(a, best, cstr__Nothing(null___)), 
                                                                                                                                        for(a, Tn, c_Set, seq([ assign(a, tn, Tn), 
                                                                                                                                                                assign(a, anf3, cstr__GetTag(tid)), 
                                                                                                                                                                assign(a, anf2, cstr__Tuple(a, anf3)), 
                                                                                                                                                                send(a, e_var(tn), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI)), anf2), 
                                                                                                                                                                recv(a, e_var(tn), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), msg_), 
                                                                                                                                                                cases(a, msg_, [ case(a, cstr__SelfSigned(X, pay), assign(a, tag, pay))], skip), 
                                                                                                                                                                cases(a, tag, [ case(a, cstr__OK(null___), skip), 
                                                                                                                                                                                case(a, cstr__TagInfo(i), skip), 
                                                                                                                                                                                case(a, cstr__TagFound(t), cases(a, t, [ case(a, cstr__Tag(ds_dy80, ds_dy81, ds_dy82), seq([ assign(a, dll__dll__brisk_anf_dyhF, ndet), 
                                                                                                                                                                                                                                                                             cases(a, dll__dll__brisk_anf_dyhF, [ case(a, cstr__Nothing(null___), seq([ assign(a, anf4, cstr__Just(ndet)), 
                                                                                                                                                                                                                                                                                                                                                        assign(a, best, anf4)])), 
                                                                                                                                                                                                                                                                                                                  case(a, cstr__Just(i), seq([ assign(a, dll__dll__brisk_anf_dyhI, ndet), 
                                                                                                                                                                                                                                                                                                                                               cases(a, dll__dll__brisk_anf_dyhI, [ case(a, cstr__False(null___), skip), 
                                                                                                                                                                                                                                                                                                                                                                                    case(a, cstr__True(null___), seq([ assign(a, anf5, cstr__Just(ndet)), 
                                                                                                                                                                                                                                                                                                                                                                                                                       assign(a, best, anf5)]))], skip)]))], skip)]))], skip)), 
                                                                                                                                                                                case(a, cstr__TagNotFound(null___), skip)], skip)])), 
                                                                                                                                        cases(a, res, [ case(a, cstr__Nothing(null___), assign(a, anf6, cstr__Nil(null___))), 
                                                                                                                                                        case(a, cstr__Just(z), assign(a, anf6, ndet))], skip), 
                                                                                                                                        assign(a, dll__dll__brisk_anf_dykO, anf6), 
                                                                                                                                        assign(a, anf8, cstr__TagRefs(dll__dll__brisk_anf_dykO)), 
                                                                                                                                        assign(a, anf7, cstr__ReplyMsg(anf8, st0)), 
                                                                                                                                        assign(a, reply, anf7)])), 
                                                                                                       case(a, cstr__AddTag(tag, refs), seq([ assign(a, anf9, cstr__ReplyMsg(cstr__OK(null___), st0)), 
                                                                                                                                              assign(a, reply, anf9)]))], skip), 
                                                                                       cases(a, reply, [ case(a, cstr__ReplyMsg(r, s_), seq([ assign(a, anf10, cstr__SelfSigned(a, r)), 
                                                                                                                                              send(a, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), anf10)])), 
                                                                                                         case(a, cstr__NoReply(s_), skip)], skip)]))], skip), 
                              assign(a, st0, s_), 
                              assign(a, loop1, 1)])), 
  TNLoop=while(C, loop0=1, seq([ assign(C, loop0, 0), 
                                            recv(C, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__TagNodeAPI))), ds_deNr), 
                                            cases(C, ds_deNr, [ case(C, cstr__Tuple(who, msg), seq([ assign(C, anf1, cstr__SelfSigned(C, cstr__OK(null___))), 
                                                                                                     send(C, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__TagNodeResponse)), anf1)]))], skip), 
                                            assign(C, st0, s_), 
                                            assign(C, loop0, 1)])),
  Rem=par([ While, sym(C,c_Set,TNLoop)]),
T=par([ seq([ cases(a, cstr__MS(ndet, ndet, 0), [ case(a, cstr__MS(ds_dy93, ds_dy94, ds_dy95), assign(a, anf0, cstr__MS(ndet, c_Set, ds_dy95)))], skip), 
            assign(a, dll__dll__brisk_anf_dyjU, anf0), 
            assign(a, st0, dll__dll__brisk_anf_dyjU), 
            seq([ assign(a, loop1, 1), While ])
                  ]), 
      sym(C, c_Set, seq([ assign(C, dll__dll__brisk_anf_drrJ, ndet), 
                          assign(C, anf0, cstr__TagState(dll__dll__brisk_anf_drrJ)), 
                          assign(C, st0, anf0), 
                          seq([ assign(C, loop0, 1), TNLoop ])])), 
      sym(B, b_Set, seq([ assign(B, dll__dll__brisk_anf_d1n, ndet), 
                          cases(B, dll__dll__brisk_anf_d1n, 
                            [ case(B, cstr__False(null___), assign(B, anf0, cstr__GetTag(cstr__TagId(ndet)))), 
                              case(B, cstr__True(null___), assign(B, anf0, cstr__AddTag(cstr__TagId(ndet), ndet)))
                            ], skip), 
                          assign(B, rpc, anf0), 
                          assign(B, anf1, cstr__Tuple(B, rpc)), 
                          send(B, e_pid(a), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__MasterAPI)), anf1), 
                          recv(B, e_pid(a), tyCon(ty__SelfSigned, tyCon(ty__MasterResponse)), msg), 
                          cases(B, msg, [ case(B, cstr__SelfSigned(X, pay), assign(B, null, pay))], skip)]))]).