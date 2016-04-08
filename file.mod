# SETS

set V;
set A within {V,V};
set K within {V,V};      #commodities


# PARAMS

param edge{V};
set K0 within K := {(s,t) in K: edge[s] == 1 and edge[t] == 1 and s <> t};
param cap{A}, >= 0;
param cardinality_dem default 1000;
param number_TCP{(s,t) in K};

param num_tratti;
param slope{1..2,1..num_tratti};

param cap_min default 1000;

param number_scenarios default 1;

param en{1..number_scenarios} default 0;

# VARS

#------------------------------------------------------------------------
#max_flow - begin
#-----------------------------------------------------------------------
param current_sorg symbolic;
param current_dest symbolic;

var fl{A,K0}, >= 0;

minimize cost:
sum{(i,j) in A,(s,t) in K0}fl[i,j,s,t];

s.t. balance_maxflow{i in V,(s,t) in K0}:
sum{(i,j) in A} fl[i,j,s,t] - sum{(j,i) in A} fl[j,i,s,t] = (
if i == s then 1
else if i == t then -1
else 0
);

param paths{(s,t) in K0,(i,j) in A} default 0;

#------------------------------------------------------------------------
#max_flow - end
#-----------------------------------------------------------------------


var f{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t } >= 0, <= cap[i,j];
var phi{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t } >= 0;

var y{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }, binary; #1 if arc (i,j) is the designated saturating arc for commodity s,t
var x{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }, binary; #1 if arc (i,j) is used for commodity s,t
var z{i in V, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t },>= 0, <= 1; #1 if node i is used for commodity s,t
var u{(i,j) in A, v in V, (s,t) in K: edge[s] == 1 && edge[t] == 1 && v <> s && s <> t}, 

binary;
var uu{(i,j) in A}, >= 0;
var tau{(i,j) in A}, >= 0;
var utility{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }, >= 0;

param bigM := 999;

# OBJECTIVE FUNCTION

maximize value_piecewise:
sum{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t}number_TCP[s,t]*utility[s,t];

maximize value_classic:
sum{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t} phi[s,t]; #- sum{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1}x[i,j,s,t];

#CONSTRAINTS

#------------------------------------------------------------------------------------------------------------------------------------
#Path Constraints

subject to ham_1{(i,j) in A, h in V,(s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s
<> t}:
u[i,j,h,s,t] <= x[i,j,s,t];

subject to ham_2{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(s,j) in A}u[s,j,h,s,t] == z[h,s,t];

subject to ham_3{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(j,s) in A}u[j,s,h,s,t] == 0;

subject to ham_4{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(j,h) in A}u[j,h,h,s,t] == z[h,s,t];

subject to ham_5{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(h,j) in A}u[h,j,h,s,t] == 0;

subject to ham_6{h in V, j in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && j <>
s && j <> h && s <> t}:
sum{(i,j) in A}u[i,j,h,s,t] == sum{(j,i) in A}u[j,i,h,s,t];

subject to ham_7{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(t,j) in A}u[t,j,h,s,t] == 0;

subject to ham_8{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && h <> s && s <> t}:
sum{(i,h) in A}x[i,h,s,t] == z[h,s,t];

#------------------------------------------------------------------------------------------------------------------------------------

#Flow Constraints

subject to balance{h in V, (s,t) in K : edge[s] == 1 && edge[t] == 1 && s <> t}:
sum{(h,j) in A}f[h,j,s,t] - sum{(j,h) in A} f[j,h,s,t] = ( if h == s then phi[s,t]
else (if h == t then -phi[s,t] else 0));

s.t. capacity{(i,j) in A}:
sum{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t } f[i,j,s,t] <= cap[i,j];

s.t. activation{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }: 

f[i,j,s,t] <= cap[i,j]*x[i,j,s,t];

s.t. degree1{i in V, (s,t) in K : edge[s] == 1 && edge[t] == 1}:
sum{(i,j) in A} x[i,j,s,t] <= 1;

s.t. degree2{(s,t) in K : edge[s] == 1 && edge[t] == 1 && s <> t}:
sum{(t,j) in A} x[t,j,s,t] <= 0;

s.t. degree3{(s,t) in K : edge[s] == 1 && edge[t] == 1 && s <> t}:
sum{(j,s) in A} x[j,s,s,t] <= 0;

s.t. two{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }:
sum{(o,d) in K: edge[o] == 1 && edge[d] == 1 && o <> d}f[i,j,o,d] >=
cap[i,j]*y[i,j,s,t];

s.t. three{(s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }:
sum{(i,j) in A} y[i,j,s,t] >= 1; #set covering

s.t. four{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }:
uu[i,j] >= f[i,j,s,t]/number_TCP[s,t];

s.t. five_b{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }:
f[i,j,s,t]/number_TCP[s,t] >= uu[i,j] - cap[i,j]*(1-y[i,j,s,t]);


#---------------------------------------------------------------------------------------------------------------------------------
s.t. bound_1{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t }:
phi[s,t]/number_TCP[s,t] >= (cap_min/cardinality_dem);

s.t. valid_1{(i,j) in A, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t}:
y[i,j,s,t] <= x[i,j,s,t];

s.t. funzione{o in 1..num_tratti, (s,t) in K: edge[s] == 1 && edge[t] == 1 && s <> t}:
utility[s,t] <= (phi[s,t]/number_TCP[s,t])*slope[1,o] + slope[2,o];


