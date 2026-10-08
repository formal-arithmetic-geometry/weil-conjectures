+++
id = "lemma-weil-pbc-level-map-tower-compatibility"
kind = "lemma"
title = "Transition compatibility of all four edges"
order = 1330
uses = ["def-weil-pbc-level-map-arrows", "lemma-weil-pbc-projection-formula-tower-compatibility"]
+++
The four corner transitions from level $n+1$ to level $n$ are

$$
\begin{aligned}
a_{n+1,n}&=Lg^*(1\otimes q_n):A_{n+1}\to A_n,\\
b_{n+1,n}&=Lg^*Rf_*(K_{n+1}\to K_n):B_{n+1}\to B_n,\\
c_{n+1,n}&=1\otimes q_n:C_{n+1}\to C_n,\\
d_{n+1,n}&=Rf'_*L(g')^*(K_{n+1}\to K_n):D_{n+1}\to D_n.
\end{aligned}
$$

Every edge is a map of towers:

$$
\begin{aligned}
b_{n+1,n}h_{n+1}&=h_na_{n+1,n},&
c_{n+1,n}v_{n+1}&=v_na_{n+1,n},\\
d_{n+1,n}h'_{n+1}&=h'_nc_{n+1,n},&
d_{n+1,n}v'_{n+1}&=v'_nb_{n+1,n}.
\end{aligned}
$$

## Proof

The first and third equations are the coefficient-tower equations for the
two projection formulas. The second follows by tensor naturality of
$\xi_K$ with respect to $q_n$. The last is naturality of the unit–counit
exchange map with respect to $K_{n+1}\to K_n$. Expanded after adjunction,
both sides of the last equation are the counit of $K$ followed by the same
coefficient quotient. Hence all four equations hold componentwise.
