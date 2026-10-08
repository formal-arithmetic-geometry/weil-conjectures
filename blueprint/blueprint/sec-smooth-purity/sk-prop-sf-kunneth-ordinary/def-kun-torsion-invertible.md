+++
id = "def-kun-torsion-invertible"
kind = "definition"
title = "Torsion objects and orders invertible in a field"
order = 1680
uses = ["def-weil-pbc-etale-sheaves"]
+++
For an etale abelian sheaf $F$ and $n\ge1$ write
$F[n]=\ker(n:F\to F)$, so that a
torsion sheaf is a sheaf whose
local sections are killed by positive integers. Let $K$ be a field
and let

$$
I_K=\{n\ge1:n\cdot1_K\ne0\},
$$

ordered by divisibility; $n\in I_K$ is called *invertible in
$K$*. A torsion sheaf on the etale site of a $K$-scheme has
*orders invertible in $K$* if every element of every geometric
stalk is killed by some $n\in I_K$. For $K$ of
characteristic $p>0$ this says the stalks have no
$p$-primary torsion; for $\operatorname{char}K=0$ it is no
condition besides torsion. A complex $K\in D(T_{\Et})$ has
*torsion cohomology with orders invertible in $K$* if every
$\mathcal H^q(K)$ has that property.
