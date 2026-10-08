+++
id = "lem-kun-fp-algebra-descent"
kind = "lemma"
title = "Descent of finitely presented algebras"
order = 1656
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $A=\varinjlim_{i\in I}A_i$ be a filtered colimit of commutative rings
with structural maps $A_i\to A$, and let $B$ be a finitely presented
$A$-algebra. Then there are an index $i$ and a finitely presented
$A_i$-algebra $B_i$ with an isomorphism of $A$-algebras
$B\cong B_i\otimes_{A_i}A$.

## Proof

A finitely presented $A$-algebra admits a finite presentation
$B\cong A[x_1,\dots,x_n]/(f_1,\dots,f_m)$ with $m,n$ finite; this is the
form of finite presentation used in
[def-weil-pbc-scheme-conventions]. Each $f_j$ has finitely many
coefficients, and each coefficient of $A$ is the image of an element of some
$A_i$; as the index set is filtered and only finitely many coefficients
occur, all of them are images of elements of a single $A_i$. Choose lifts
$\tilde f_1,\dots,\tilde f_m\in A_i[x_1,\dots,x_n]$ of the $f_j$ and put

$$
B_i=A_i[x_1,\dots,x_n]/(\tilde f_1,\dots,\tilde f_m),
$$

a finitely presented $A_i$-algebra. Base change along $A_i\to A$ commutes
with polynomial rings and with forming quotients, so

$$
B_i\otimes_{A_i}A\cong A[x_1,\dots,x_n]/(f_1,\dots,f_m)\cong B,
$$

which is the assertion.
