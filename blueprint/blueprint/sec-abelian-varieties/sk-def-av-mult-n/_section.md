+++
id = "sk-def-av-mult-n"
kind = "section"
title = "Multiplication by $n$ and $n$-torsion"
lean = ["AlgebraicGeometry.torsionSubgroupScheme"]
order = 433
+++
*Definition (sketch).*

Let $A$ be an abelian variety over $k$ and $n\ge1$. The $n$-th
*multiplication map* $[n]:A\to A$ is the homomorphism given on
points by $a\mapsto a+\dots+a$ ($n$ summands), and the $n$-th
*torsion subgroup scheme* is

$$
A[n]:=\ker\bigl([n]\bigr)\subseteq A,
$$

a closed subgroup scheme of $A$ ([sk-def-av-group-scheme]); we write
$A(k)[n]=A[n](k)$ for the group of $k$-points of the kernel.
