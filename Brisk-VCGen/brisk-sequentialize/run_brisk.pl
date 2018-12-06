:- use_module(library(terms)).
:- use_module(library(process)).
:- consult([rewrite]).

user:runtime_entry(start) :-
    prolog_flag(argv, [Fn | _])  ->
       consult([Fn]),
       ( current_predicate(prog/5), prog( Name, Decls, Ensures, P, Rem )
       ; current_predicate(prog/4), prog( Name, Decls, Ensures, P ), Rem=skip
       ),

       current_output(Out), open_null_stream(Null),

       /** Do the rewriting **/
       set_output(Null),
       check_race_freedom(P, P1),
       !,
       rewrite(P1, Rem, X, _),
       set_output(Out),

       portray_clause(prog( Name, Decls, Ensures, X )),

       halt(0).
