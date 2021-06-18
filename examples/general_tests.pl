
?- abolish_all_tables.

test(X):- test(X,_).
%%Evaluates Lit, finding the greatest undefined value (meta_tu) and the greatest true value (para_t)
test(Lit,_):- 
%  meta(Lit),
  para_t(Lit),
%  pc_true(Lit),
  fail.
test(Lit,Resid):- 
  Lit = A~W,
  get_residual(para_t_1(A,W),Resid).

%------------------------------------------------------------------------

p_1 if a \ meet(0.8).

d if a.
d if b.

d_1 if a.			% Test mix of fact plus rules
d_1~0.8.

c if a,b.
c_1 if a_1,b.			% Test calling a rule
c_3 if a~M1,M1 > 0.7,b.		% Test call w. strength
c_4 if a_1,naf(b~1).		% Test calling a rule + negation

a~0.9.
a_1 if a,true.			% Test call with non-quant literal.
%a_2 if naf(a),true.		% Test negation

b~0.8.

% Tests of rule weights
c_b_1 if a,b \ boost(0).
c_b_2 if a,b \ boost(0.1).

rec_boost if rec_boost \ boost(0.1).
rec_boost~0.7.

%e_und if undefined \ abs(0.8).
e_und~0.8 if undefined.
e_und~0.7.

% Cannot currently call with ground weight in the body of a rule.
c_2 if a_1~0.3,b.			% Test calling a rule

n_0~0.4.
n_0~0.5.

n_1~0.4.
n_1~0.5.
neg(n_1)~0.5.

p_2 if n_1.


nn_1~0.6.
neg(nn_1)~0.6.

nn_u if naf(nn_1~0.5).
neg(nn_u) if naf(nn_1~0.5).

nn_f if naf(nn_1~0.4).
neg(nn_f) if naf(nn_1~0.4).

nn_t if naf(nn_1~0.8).
%neg(nn_t) if naf(nn_1~0.8).


t~0.4.
t~0.5.
t~0.6:- undefined.

%----------------------------------------------------------------------

pc_1a~0.4.
neg(pc_1a)~0.7.

pc_1b~0.6.
neg(pc_1b)~0.6.

pc_2 if pc_1a.

pc_3 if pc_1b.
pc_3~0.7.

pc_4~0.5.
neg(pc_4)~0.5.

    

d_c_1 if pc_1a.
d_c_1 if pc_1b.

rec_boost_c if rec_boost_c \ boost(0.1).
rec_boost_c~0.7.

neg(rec_boost_c)~0.2.

cyc_c if cyc_b.
neg(cyc_c)~0.6.

cyc_b if cyc_c.
cyc_b~0.5.

neg(cyc_b_1) if neg(cyc_c).
cyc_b_1~0.5.

%-------------

test:- abolish_all_tables,fail.
test:- test_fuzzy_consist,writeln(fuzzy_consist_tests_passed),fail.
%test:- test_ind,writeln(independent_tests_passed),fail.
test:- test_disjoint_consist,writeln(disjoint_consist_tests_passed),fail.
test:- test_fuzzy_para,writeln(fuzzy_para_tests_passed).

test_fuzzy_consist:- abolish_all_tables,fail.
test_fuzzy_consist:- set_tnorm(fuzzy),fail.
test_fuzzy_consist:- meta_t(a~X),(X = 0.9 -> true ; abort(error_fuzzy(a~X))),fail.
test_fuzzy_consist:- meta_t(a_1~X),(X = 0.9 -> true ; abort(error_fuzzy(a~X))),fail.
test_fuzzy_consist:- meta_t(c~X),(X = 0.8 -> true ; abort(error_fuzzy(c~X))),fail.
test_fuzzy_consist:- meta_t(c_1~X),(X = 0.8 -> true ; abort(error_fuzzy(c_1~X))),fail.
test_fuzzy_consist:- meta_t(c_3~X),(X = 0.8 -> true ; abort(error_fuzzy(c_3~X))),fail.
%test_fuzzy_consist:- writeln(here).
test_fuzzy_consist:- meta_t(c_4~X),(equal_at_precision(X,0.9,3) -> true ; abort(error_fuzzy(c_4~X))),fail.
%test_fuzzy_consist:- writeln(here).
test_fuzzy_consist:- meta_t(d~X),(X = 0.9 -> true ; abort(error_fuzzy(d~X))),fail.
test_fuzzy_consist:- meta_t(d_1~X),(X = 0.9 -> true ; abort(error_fuzzy(d_1~X))),fail.
test_fuzzy_consist:- meta_t(n_1~_X),fail.
%test_fuzzy:- get_tval(n_1,L),(L = [0.4 - t, 0.5 - u] -> true ; abort(error_fuzzy(n_1~L))),fail.
test_fuzzy_consist:- meta_t(occurs(e1,6)~_X),fail.
test_fuzzy_consist:- meta_t(c_b_1~X),(equal_at_precision(X,0.8,3) -> true ; abort(error_fuzzy_cons(c_b_1~X))),fail.
test_fuzzy_consist:- meta_t(c_b_2~X),(equal_at_precision(X,0.88,3) -> true ; abort(error_fuzzy_cons(c_b_2~X))),fail.
test_fuzzy_consist:- meta_t(rec_boost~X),(equal_at_precision(X,1,3) -> true ; abort(error_fuzzy_cons(c_b_2~X))),fail.
test_fuzzy_consist.

test_disjoint_consist:- abolish_all_tables,fail.
test_disjoint_consist:- set_tnorm(disjoint),fail.
test_disjoint_consist:- meta_t(a~X),(equal_at_precision(X,0.9,3) -> true ; abort(error_disjoint(a~X))),fail.
test_disjoint_consist:- meta_t(c~X),(X = 0.7 -> true ; abort(error_disjoint(c~X))),fail.
test_disjoint_consist:- meta_t(d~X),(X = 1 -> true ; abort(error_disjoint(d~X))),fail.
test_disjoint_consist.


test_fuzzy_para:- abolish_all_tables,fail.
test_fuzzy_para:- set_tnorm(fuzzy),fail.
test_fuzzy_para:- test(pc_1a~X),(equal_at_precision(X,0.3,3) -> true ; abort(error_fuzzy_para(pc_1~X))),fail.
test_fuzzy_para:- test(pc_2~X),(equal_at_precision(X,0.3,3) -> true ; abort(error_fuzzy_para(pc_2~X))),fail.
test_fuzzy_para:- test(pc_3~X),(equal_at_precision(X,0.7,3) -> true ; abort(error_fuzzy_para(pc_3~X))),fail.
test_fuzzy_para:- test(rec_boost_c~X),(equal_at_precision(X,0.8,3) -> true ; abort(error_fzy_p(rec_boost_c~X))),fail.
test_fuzzy_para:- test(cyc_b~X),(equal_at_precision(X,0.5,3) -> true ; abort(error_fuzzy_para(cyc_b~X))),fail.
test_fuzzy_para:- test(cyc_b_1~X),(equal_at_precision(X,0.4,3) -> true ; abort(error_fuzzy_para(cyc_b_1~X))),fail.
test_fuzzy_para:- test(cyc_c~X),(equal_at_precision(X,0.4,3) -> true ; abort(error_fuzzy_para(cyc_c~X))),fail.
test_fuzzy_para:- test(nn_t~X,[]),(equal_at_precision(X,1,3) -> true ; abort(error_fuzzy_para(nn_t~X))),fail.
test_fuzzy_para:- test(nn_u~X,Resid),Resid \== [],(kinda_equal(X,1) -> true ; abort(error_fuzzy_para(nn_u~X))),fail.
test_fuzzy_para:- test(nn_f~X,Resid),Resid \== [], (kinda_equal(X,1) -> true ; abort(error_fuzzy_para(nn_f~X))),fail.
test_fuzzy_para.

kinda_equal(X,Y):- equal_at_precision(X,Y,3).

end_of_file.

/*
test_ind:- abolish_all_tables,fail.
test_ind:- set_tnorm(independent),fail.
test_ind:- meta(a~X),    (X = 0.9 -> true ; abort(error_independent(a~X))),fail.
test_ind:- meta(c~X),    (equal_at_precision(X,0.72,3) -> true ; abort(error_independent(c~X))),fail.
test_ind:- meta(c_4~X),  (equal_at_precision(X,0.18,3) -> true ; abort(error_independent(c_4~X))),fail.
test_ind:- meta(d~X),    (X = 0.98 -> true ; abort(error_independent(d~X))),fail.
test_ind.
*/

| ?- X is 0.8 * 0.9,write_canonical(X).
0.72000000000000008
X = 0.72

SWI

X is 0.8 * 0.9,write_canonical(X).
0.7200000000000001
X = 0.7200000000000001.


