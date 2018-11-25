%%% Todo %%%
%% Continuous Variables (Belle, Edinburgh)
%% Correlation between 0 and 1 for tnorms 
%% Get some good examples of independent
%% Add in skeptical
%% Test naf with para_t
%%%%%%%%%%%%

:- import check_ground/3,check_nonvar/3 from error_handler.
:- import memberchk/2 from basics.

:- op(1200,xfx,if).
:- op(1100,xfx,\).
:- op(500,xfx,~).

?- abolish_all_tables.

:- dynamic mytrace/1.
%mytrace(on).
db_start:- assert(mytrace(on)).
db_stop:- retractall(mytrace(on)).

:- dynamic current_tnorm/1.
current_tnorm(fuzzy).
?- writeln(current_tnorm(fuzzy)).

naf(X):- \+(X).
%-------------------------------------------------------

meta(A~M):- 
   meta_tu(A~M),fail.
%meta(A~M):- 
%   meta_t(A~M),fail.
%meta(A~M):- 
%   meta_t(neg(A)~M),fail.
meta(_).

% Find the greatest value M at which A is true (if any > 0).
para_t(A~M):- !,
	    meta_debug(calling(para_t(A~M))),
	    (var(M) -> 
	      para_t_1(A,M)
	    ; para_t_1(A,M1),
	      % meet(M,M1,M) (wont work due to Prolog problems)
	      M1 >= M). 

:- table para_t_1(_,lattice(join(X,Y,Z))).
para_t_1(A,M):- 
	  if(A,B),
	  get_rule_weight(B,Body,Weight),
          meta_debug(calling(if(A,Body))),
	  para_t(Body,1,M_b),
	  apply_rule_weight(Weight,M_b,M_1),
	  get_complement(A~1,Compl,_M_c),
	  (  meta_t(Compl~M_c),
	     (1-M_c < M_1 -> M is 1-M_c ; M = M_1),M > 0
	   ; 
	     sk_not(meta_t(Compl~_)),M = M_1),
          meta_debug(succeeded(if(A,Body,M))).
para_t_1(A,M):- 
        meta_debug(calling(para_t_1(A,M))),
	A~M_fact,
	   get_complement(A~1,Compl,_M_c),
	(  meta_t(Compl~M_c),
	   (1-M_c < M_fact -> M is 1-M_c ; M_fact = M)
         ; 
	   sk_not(meta_t(Compl~_)),M_fact = M),
        meta_debug(succeeded(meta_1_t(A,M))).

para_t(','(A,B),M_in,M_out):- !,
	meta_debug(calling(para_t3(A,M_in))),
	para_t(A,M_in,M_mid),
	meta_debug(calling(para_t3(B))),
	para_t(B,M_mid,M_out).
% Assuming input is ground.  Can expand later
para_t(naf(A~M),M_in,M_in):- !,
	meta_debug(calling(para_t3(A,M_in))),
        sk_not(para_t(A~M)).
para_t((A;B),M_in,M_out):- !,
      abort('Disjunction not allowed within the body of a quantified rule.').
para_t(A,M_in,M_out):- 
        (is_quant(A,CallTerm) -> 
	   meta_debug(calling(para_t3(A,M_in,M_out))),
	   para_t(CallTerm),
	   CallTerm = _~M_mid
	 ; call(A),get_top(M_mid)),
	meet(M_in,M_mid,M_out).

%-------------------------------------------------------

% Derivation of A w.o. considering neg(A) so it gives an over-estimate
% of the truth of A.  A may not be true at M if paraconsistent, but
% neg(A) cannot be true at weight greater than 1-A, which is how this
% is used (by para_t).

meta_t(A~M):- !,
	    meta_debug(calling(meta_t(A~M))),
	    (var(M) -> 
	      meta_1_t(A,M)
	    ; meta_1_t(A,M1),
	      % meet(M,M1,M) (wont work due to Prolog problems)
	      M1 >= M). 

:- table meta_1_t(_,lattice(join(X,Y,Z))).
meta_1_t(A,M):- 
	  if(A,B),
	  get_rule_weight(B,Body,Weight),
          meta_debug(calling(if(A,Body))),
	  meta_t(Body,1,M_b),
          meta_debug(succeeded(if(A,Body,M_b))),
	  apply_rule_weight(Weight,M_b,M).
meta_1_t(A,M):- 
        meta_debug(calling(meta_1_t(A,M))),
	A~M,
        meta_debug(succeeded(meta_1_t(A,M))).

meta_t(','(A,B),M_in,M_out):- !,
	meta_debug(calling(meta3_t(A))),
	meta_t(A,M_in,M_mid),
	meta_debug(calling(meta3_t(B))),
	meta_t(B,M_mid,M_out).
% Assuming input is ground.  Can expand later
meta_t(naf(A~M),M_in,M_in):- !,
     sk_not(meta_tu(A~M)).
%meta_t(neg(A),M_in,M_out):- !,
%	meta_debug(calling(meta(neg(A),M_in,M_out))),
%	meta(CallTerm),
%	CallTerm = _~M_mid,
%	meet(M_in,M_mid,M_out).
%	   M_c is 1 - M_mid,
%	   sk_not(meta(A~M_c))
meta_t(A,M_in,M_out):- 
        (is_quant(A,CallTerm) -> 
	   meta_debug(calling(A,M_in,M_out)),
	   meta_t(CallTerm),
	   CallTerm = _~M_mid
%	   M_c is 1 - M_mid,
%	   sk_not(meta(neg(A)~M_c))
	 ; call(A),get_top(M_mid)),
	meet(M_in,M_mid,M_out).
	
%-------------------------------------------------------
% Succeeds if A is true or undefined at weight M.

meta_tu(A~M):- !,
	    meta_debug(calling(meta_tu(A~M))),
	    (var(M) -> 
	      meta_1_tu(A,M)
	    ; meta_1_tu(A,M1),
	      % meet(M,M1,M) (wont work due to Prolog problems)
	      M1 >= M). 

:- table meta_1_tu(_,lattice(join(X,Y,Z))).
meta_1_tu(A,M):- 
	  if(A,B),
	  get_rule_weight(B,Body,Weight),
          meta_debug(calling(if(A,Body))),
	  meta_tu(Body,1,M_b),
          meta_debug(succeeded(if(A,Body,M_b))),
	  apply_rule_weight(Weight,M_b,M),
	  get_complement(A~M,Compl,M_c),
	  sk_not(meta_tu(Compl~M_c)),
	  meta_debug(succeeded(meta_1_tu(A,M))).
meta_1_tu(A,M):- 
        meta_debug(calling(meta_1_tu(A,M))),
	A~M,
        get_complement(A~M,Compl,M_c),
	sk_not(meta_tu(Compl~M_c)),
        meta_debug(succeeded(meta_1_tu(A,M))).

meta_tu(','(A,B),M_in,M_out):- !,
	meta_debug(calling(meta3(A))),
	meta_tu(A,M_in,M_mid),
	meta_debug(calling(meta3(B))),
	meta_tu(B,M_mid,M_out).
meta_tu(naf(A~M),M_in,M_in):- !,
     sk_not(meta_t(A~M)).
%meta_t(neg(A),M_in,M_out):- !,
%	meta_debug(calling(meta(neg(A),M_in,M_out))),
%	meta(CallTerm),
%	CallTerm = _~M_mid,
%	meet(M_in,M_mid,M_out).
%	   M_c is 1 - M_mid,
%	   sk_not(meta(A~M_c))
meta_tu(A,M_in,M_out):- 
        (is_quant(A,CallTerm) -> 
	   meta_debug(calling(A,M_in,M_out)),
	   meta_tu(CallTerm),
	   CallTerm = _~M_mid
%	   M_c is 1 - M_mid,
%	   sk_not(meta(neg(A)~M_c))
	 ; call(A),get_top(M_mid)),
	meet(M_in,M_mid,M_out).
	
call_t_complement(A~_M,M_c):- 
   get_complement(A~1,Compl,_M_c),
   (meta_1_t(Compl,_),fail ; true),
   get_residual(meta_1_t(Compl,M_c),[]).
call_t_complement(A,0):- 
   get_complement(A~1,Compl,_M_c),
   \+ get_residual(meta_1_t(Compl,_),[]).

%-------------------------------------------------------

get_complement(neg(A)~M,A,M_c):-!,M_c is 1 - M.
get_complement(A~M,neg(A),M_c):-!,M_c is 1 - M.

get_complement(neg(A),A):-!.
get_complement(A,neg(A)):-!.

is_quant(A~M,A~M):- !.
is_quant(A,A~_M):- A~_,!.
is_quant(A,A~_M):- if(A,_),!.

apply_rule_weight(none,M_b,M_b).
apply_rule_weight(boost(B),M_b,M):- M is min(1,M_b + M_b*B).
apply_rule_weight(abs(M),_M_b,M).
apply_rule_weight(meet(B),M_b,M):- meet(B,M_b,M).
apply_rule_weight(logistic,M_b,M):- M is 1 / (1 + e**(-(12*M_b-6))).

get_rule_weight(\(Body,Weight),Body,Weight):- !.
get_rule_weight(Body,Body,none).

get_top(1).

/* Independent works, but it assumes exclusivity of derivations, so its tricky to use */

meet(A,B,C):- 
     (current_tnorm(fuzzy) -> (A > B -> C=B ; C=A)
     ; current_tnorm(independent) -> (C is A * B)
     ; current_tnorm(disjoint) -> ((0 > A + B - 1) -> C = 0 ; C is A+B-1)).
%     ; current_tnorm(disjoint) -> ((0 > A + B - 1) -> C = 0 ; C is A+B-1)).

join(A,B,C):- 
     (current_tnorm(fuzzy) -> (A > B -> C=A ; C=B)
     ; current_tnorm(independent) -> C is 1 - ( (1-A) * (1 - B))
     ; current_tnorm(disjoint) -> ((A + B > 1) -> C = 1 ; C is A + B)).

clear:- abolish_all_tables.

set_fuzzy:- set_tnorm(fuzzy).
set_coinciding:- set_tnorm(fuzzy).
set_independent:- set_tnorm(independent).
set_disjoint:- set_tnorm(disjoint).

set_tnorm(Norm):- 
    (memberchk(Norm,[fuzzy,independent,disjoint]) -> 
       true 
     ; abort((Norm,'is not one of fuzzy,independent,disjoint'))),
    abolish_all_tables,
    retractall(current_tnorm(_)),
    assert(current_tnorm(Norm)).

% to handle problems w. floating point precision
equal_at_precision(X,Y,N):- 
	round(X*(10**N)) =:= round(Y*(10**N)).

meta_debug(Atom):- 
	(mytrace(on) -> writeln(Atom) ; true). 

%------------------------------------------------------------------------------------------------
end_of_file.

%%% Old code and scratchpad


%meta_1(','(A,B),M):- !,
%	    meta_test(called(meta_1(A,M))),
%	    meta(A~_M1,1,M_out),
%	    (var(M) -> M_out = M ;  M_out > M).

para_t(A~M,true):- 
   get_residual(meta_1_t(A,M_t),[]),
%   meta_t(A~M_t),
   call_t_complement(A~M,M_c),
   (1- M_c < M_t -> M is 1 - M_c ; M = M_t).
para_t(A~M,u):- 
   get_residual(meta_1_tu(A,M),R),R \= [].

_1_t(A,M):- 
	  if(A,B),
	  get_rule_weight(B,Body,Weight),
          meta_debug(calling(if(A,Body))),
	  meta_t(Body,1,M_b),
          meta_debug(succeeded(if(A,Body,M_b))),
	  apply_rule_weight(Weight,M_b,M).


call_compliment(A,M):- 
	get_complement(A~M,Compl_A,M_c),
	sk_not(meta(Compl_A~M_c)),
	fail.
call_compliment(_A,_M).

%model(A,T,U,F):- 
%  get_true(A,T).


get_true(A,T):- 
  get_residual(meta_1(A,M_t),[]),
  get_complement(A,Compl_A),
  get_max_tu(Compl_A,M_c),
  (M_t < (1-M_c) -> T is M_t ; T is 1-M_c).

get_max_tu(Lit,V):- 
	setof(W,R^(get_residual(meta_1(Lit,W),R)),Vs),
	last(Vs,V).

last([V],V):-!.
last([_|T],V):- last(T,V).

get_tval(Lit,List):- 
	setof(W-T,Resid^(get_residual(meta_1(Lit,W),Resid),
	                 (Resid = [] -> T = t ; T = u)),List).

% var exceptions below
get_measure(A,M):- 
	check_ground(A,get_measure/1,1),
	(A = _A1~M1 -> M = M1 ; get_top(M)).

