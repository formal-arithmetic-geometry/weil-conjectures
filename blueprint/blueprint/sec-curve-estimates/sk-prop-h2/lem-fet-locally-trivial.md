+++
id = "lem-fet-locally-trivial"
kind = "theorem"
title = "Finite etale covers are trivial after an etale base change"
order = 965
uses = ["def-galois-categories", "def-weil-pbc-scheme-conventions"]
+++
Let $P\to Y$ be finite etale. Then there is a surjective etale
$Y'\to Y$ and a finite set $S$ with
$P\times_YY'\cong Y'\times S$ over $Y'$.

## Proof

Step 1: the strictly local case. Let $(A,\mathfrak m)$ be a strictly
henselian local ring and $B$ a finite etale $A$-algebra (finite
etale morphisms being those of [def-galois-categories] and
[def-weil-pbc-scheme-conventions]). Then $B$ is
finite locally free over $A$; let $n$ be its rank. The reduction
$B/\mathfrak mB$ is a finite etale algebra over the separably closed
field $A/\mathfrak m$, hence a finite product of copies of that field (a
finite etale algebra over a field is a product of finite separable field
extensions, and over a separably closed field each of these is the field).
Choose $b_1,\dots,b_n\in B$ lifting a basis; the induced $A$-algebra
map $A^n\to B$ is surjective by Nakayama's lemma, and both sides are free
of rank $n$, so it is an isomorphism.
Step 2: the general case. Let $y\in Y$ and $A=\mathcal O_{Y,\bar y}^{sh}$, the strict henselization, which is the filtered
colimit of the rings of the etale neighbourhoods $Y'\to Y$ of $y$. By
Step 1 the finite etale $A$-algebra
$B=\Gamma(P\times_Y\operatorname{Spec}A,\mathcal O)$ is isomorphic to
$A^n$. The isomorphism is given by finitely many elements and relations,
so by the standard limit argument for finitely presented data it descends
to an etale neighbourhood: there is a factorization $y\to Y'\to Y$ with
$Y'\to Y$ etale and $P\times_YY'\cong Y'\times\{1,\dots,n\}$.
Step 3: conclusion. The neighbourhoods obtained in Step 2 for all points
$y\in Y$ form a covering family of etale morphisms; their disjoint union
is a surjective etale $Y'\to Y$ trivializing $P$.
