?- abolish_all_tables.
?- set_minmax.

test(X):- test(X,_).
%%Evaluates Lit, finding the greatest undefined value (meta_tu) and the greatest true value (para_t)
test(Lit,_):- 
%  meta(Lit),
  para_t(Lit),
  fail.
test(Lit,Resid):- 
  Lit = A~W,
  get_residual(para_t_1(A,W),Resid).

%------------------------------------------------------------------------

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

pc_1a~[0.4,0.4].
neg(pc_1a)~[0.7,0.7].

pc_1b~[0.6,0.6].
neg(pc_1b)~[0.6,0.6].

pc_2 if pc_1a.

pc_3 if pc_1b.
pc_3~[0.7,0.7].

cyc_c if cyc_b.
neg(cyc_c)~[0.6,0.6].

cyc_b if cyc_c.
cyc_b~[0.5,0.5].

test_minmax:- abolish_all_tables,fail.
test_minmax:- set_tnorm(minmax),fail.
test_minmax:- meta_t(a~X),(X = [0.9,0.9] -> true ; abort(error_minmax(a~X))),fail.
test_minmax:- meta_t(a_1~X),(equal_at_precision(X,[0.9,0.9],3) -> true ; abort(error_minmax(a_1~X))),fail.
test_minmax:- meta_t(c~X),(equal_at_precision(X,[0.7,0.8],3) -> true   ; abort(error_minmax(c~X))),fail.
test_minmax:- meta_t(c_1~X),(equal_at_precision(X,[0.7,0.8],3) -> true ; abort(error_minmax(c_1~X))),fail.
test_minmax:- meta_t(c_3~X),(equal_at_precision(X,[0.7,0.8],3) -> true ; abort(error_minmax(c_3~X))),fail.
test_minmax:- meta_t(c_4~X),(equal_at_precision(X,[0.9,0.9],3) -> true ; abort(error_minmax(c_4~X))),fail.
test_minmax:- meta_t(d~X),(equal_at_precision(X,[0.9,1],3) -> true     ; abort(error_minmax(d~X))),fail.
test_minmax:- meta_t(d_1~X),(equal_at_precision(X,[0.9,1],3) -> true   ; abort(error_minmax(d_1~X))),fail.
%test_minmax:- meta_t(n_1~_X),fail.
%test_minmax:- meta_t(occurs(e1,6)~_X),fail.
%%test_minmax:- meta_t(c_b_1~X),(equal_at_precision(X,0.8,3) -> true ; abort(error_minmax_cons(c_b_1~X))),fail.
%test_minmax:- meta_t(c_b_2~X),(equal_at_precision(X,0.88,3) -> true ; abort(error_minmax_cons(c_b_2~X))),fail.
%test_minmax:- meta_t(rec_boost~X),(equal_at_precision(X,1,3) -> true ; abort(error_minmax_cons(c_b_2~X))),fail.
test_minmax:- writeln(test_minmax_passed).

test_minmax_para:- abolish_all_tables,fail.
test_minmax_para:- set_tnorm(minmax),fail.
test_minmax_para:- test(pc_1a~X),(equal_at_precision(X,[0.3,0.3],3) -> true ; abort(error_minmax_para(pc_1~X))),fail.
test_minmax_para:- test(pc_2~X),(equal_at_precision(X,[0.3,0.3],3) -> true ; abort(error_minmax_para(pc_2~X))),fail.
test_minmax_para:- test(pc_3~X),(equal_at_precision(X,[0.7,1],3) -> true ; abort(error_minmax_para(pc_3~X))),fail.
%test_minmax_para:- test(rec_boost_c~X),(equal_at_precision(X,0.8,3) -> true ; abort(error_fzy_p(rec_boost_c~X))),fail.
test_minmax_para:- test(cyc_b~X),(equal_at_precision(X,0.5,3) -> true ; abort(error_minmax_para(cyc_b~X))),fail.
test_minmax_para:- test(cyc_c~X),(equal_at_precision(X,0.4,3) -> true ; abort(error_minmax_para(cyc_c~X))),fail.
test_minmax_para.
end_of_file.
test_minmax_para:- test(nn_t~X,[]),(equal_at_precision(X,1,3) -> true ; abort(error_minmax_para(nn_t~X))),fail.
test_minmax_para:- test(nn_u~X,Resid),Resid \== [],(kinda_equal(X,1) -> true ; abort(error_minmax_para(nn_f~X))),fail.
test_minmax_para:- test(nn_f~X,_), abort(error_minmax_para(nn_f~X)),fail.
