+++
id = "lem-galois-geometric-fibre"
kind = "lemma"
title = "The geometric fibre of a finite etale cover"
order = 584
uses = ["def-galois-categories"]
+++
Let $Y$ be a scheme with a geometric point $\bar y\to Y$, and let
$P\to Y$ be an object of $\mathrm{F\acute Et}(Y)$ as in
[def-galois-categories]. Then $P\times_Y\bar y$ is a finite
disjoint union of copies of $\bar y$; in particular $|P_{\bar y}|$
is a finite set.

## Proof

By [def-galois-categories] the morphism $P\to Y$ is finite
etale, hence so is its base change $P\times_Y\bar y\to\bar y$. Write
$\bar y=\operatorname{Spec}k$ with $k$ separably closed; then
$P\times_Y\bar y=\operatorname{Spec}B$ for a finite etale
$k$-algebra $B$, and a finite etale algebra over a separably closed
field is a finite product of copies of that field (an elementary
structural input; it is used again in Step 1 of the triviality theorem
proved below). Hence $B\cong k^n$ for $n=\dim_kB$, and
$P\times_Y\bar y$ is a finite disjoint union of copies of
$\bar y$.
