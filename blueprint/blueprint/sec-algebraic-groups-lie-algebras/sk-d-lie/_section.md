+++
id = "sk-d-lie"
kind = "section"
title = "Lie algebras, radicals and centers"
order = 2462
uses = ["sk-d-linear"]
lean = ["LieAlgebra.radical", "LieAlgebra.center", "LieAlgebra.HasCentralRadical", "killingForm"]
+++
*Definition (sketch).*

A Lie algebra is a $k$-vector space $L$ with a
bilinear alternating bracket satisfying the Jacobi identity.
An ideal $I$ satisfies $[L,I]\subseteq I$. Write $[I,I]$ for the span
of its brackets. The derived sequence is $D^0I=I$,
$D^{n+1}I=[D^nI,D^nI]$; $I$ is solvable if some $D^nI=0$.
The radical $\rad L$ is the sum of all solvable ideals, and the center
is $Z(L)=\{x:[x,L]=0\}$. A central radical means $\rad L=Z(L)$.
A Lie representation $r:L\to\End(V)$ is linear with
$r([x,y])=r(x)r(y)-r(y)r(x)$. Lie-invariance means $r(L)U\subseteq U$;
simple, semisimple and faithful have the corresponding meanings.
The quotient $L/I$ has bracket induced from $L$, and the Killing form is
$B_L(x,y)=\Tr(\operatorname{ad}(x)\operatorname{ad}(y))$, where
$\operatorname{ad}(x)y=[x,y]$. A Lie algebra is perfect if $L=[L,L]$.

Uses: [sk-d-linear]
