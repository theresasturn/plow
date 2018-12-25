?- abolish_all_tables.
?- set_minmax.

c if a,b.
c_1 if a_1,b.    			% Test calling a rule
c_3 if a~M,M=[L,_H],L > 0.7,b.		% Test call w. strength
c_4 if a_1,naf(b~[1,1]).	        % Test calling a rule + negation

a~[0.9,0.9].
b~[0.8,0.8].

d if a.
d if b.

d_1 if a.			% Test mix of fact plus rules
d_1~[0.8,0.8].

a_1 if a,true.		        	% Test call with non-quant literal.

test:- abolish_all_tables,fail.
test:- set_tnorm(minmax),fail.
test:- meta_t(a~X),(X = [0.9,0.9] -> true ; abort(error_fuzzy(a~X))),fail.
test:- meta_t(a_1~X),(equal_at_precision(X,[0.9,0.9],3) -> true ; abort(error_fuzzy(a_1~X))),fail.
test:- meta_t(c~X),(equal_at_precision(X,[0.7,0.8],3) -> true   ; abort(error_fuzzy(c~X))),fail.
test:- meta_t(c_1~X),(equal_at_precision(X,[0.7,0.8],3) -> true ; abort(error_fuzzy(c_1~X))),fail.
test:- meta_t(c_3~X),(equal_at_precision(X,[0.7,0.8],3) -> true ; abort(error_fuzzy(c_3~X))),fail.
test:- meta_t(c_4~X),(equal_at_precision(X,[0.9,0.9],3) -> true ; abort(error_fuzzy(c_4~X))),fail.
test:- meta_t(d~X),(equal_at_precision(X,[0.9,1],3) -> true     ; abort(error_fuzzy(d~X))),fail.
test:- meta_t(d_1~X),(equal_at_precision(X,[0.9,1],3) -> true   ; abort(error_fuzzy(d_1~X))),fail.
%test:- meta_t(n_1~_X),fail.
%test:- meta_t(occurs(e1,6)~_X),fail.
%%test:- meta_t(c_b_1~X),(equal_at_precision(X,0.8,3) -> true ; abort(error_fuzzy_cons(c_b_1~X))),fail.
%test:- meta_t(c_b_2~X),(equal_at_precision(X,0.88,3) -> true ; abort(error_fuzzy_cons(c_b_2~X))),fail.
%test:- meta_t(rec_boost~X),(equal_at_precision(X,1,3) -> true ; abort(error_fuzzy_cons(c_b_2~X))),fail.
test:- writeln(minmax_tests_passed).
