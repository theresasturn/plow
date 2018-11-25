%--------------------------------
%Skipping Restraint

:- table ~(_,lattice(join(X,Y,Z))).
occurs(e1,0)~1.
occurs(E,T)~P:- 
	T >= 0,integer(T),
	horizon(Bound),
	T =< Bound,
	T1 is T-1,
	occurs(E,T1)~P1,
	P is 0.99*P1.
occurs(E,T)~0.5:- 
	horizon(Bound),
	T > Bound,
	occurs(E,Bound)~_,
	T =< 2*Bound.
occurs(E,T)~1:- 
	horizon(Bound),
	T > Bound,
	occurs(E,Bound)~_,
	undefined.

horizon(4).
/*
T:0  - 0-1 true
T:1  - 0-0.99 true ; 0.99 - 1 false
T:11 - 0.0.5 true ; 0.5 - 1 u.
T:21 - 0-1 u.
*/

test:- abolish_all_tables,fail.
test:- set_fuzzy,fail.
test:- occurs(e1,6)~_,fail.
test:- restr_tv( occurs( e1,6 ),G ),(L = [0.5 - t,1 - u] -> true ; abort(error_restr(occurs(e1,6)~L))),fail.
test:- writeln(passed(occurs)).


%----------------------------------------------------------------
end_of_file.

-- 

Teri to write the truth_value meta interpreter.

truth_value(p(X),From,To):- 
	look at the table for p(X)
	look at the table for neg_p(X)
	find the intervals.

------------------------------------------------------------------------------

project(E,0)~1.
project(E,T)~P:- 
	T >= 0,integer(T),
	first_hundred_days(T),
	T1 is T-1,
	project(E,T1)~P1,P is 0.9999*P1.
project(E,T)~P:- 
	T >= 0,integer(T),
	second_hundred_days(T),
	undefined.
neg_project(E,T)~P:- 
	T >= 0,integer(T),
	second_hundred_days(T),
	P is 0.9999**100.

------------------------------------------------------------------------------
Can do this via tnorm logic or loss logic

if basic_vocab 1-N1
if not-basic_vocab 1-(Number of Syllables * N2) (N2 < N1) 
if complex_grammar 1-(Cognitive_Confusion)
if greater than 30 words undefined

------------------------

corr(X,Y) = 0.5

0.5 = E[(X-mx)(Y-my)] / \sigma_x*\sigma_y 

0.5 * \sigma_x*\sigma_y = E[(X-mx)(Y-my)] 

-------------------------
Define cglp
Supporting XSB_Q

cglog -> cglog_lp (supporting cglp)

cglp -- XSB-quant
nlp -> cglog -> cglog-lp -> cglp -> cogmem