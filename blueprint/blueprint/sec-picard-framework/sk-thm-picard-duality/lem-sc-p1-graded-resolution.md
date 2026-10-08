+++
id = "lem-sc-p1-graded-resolution"
kind = "lemma"
title = "Resolutions by twists on $\\mathbf P^1_k$"
order = 691
uses = ["def-sc-p1-standard", "lem-sc-p1-twist-exists"]
+++
Let $k$ be a field and $\mathcal G$ a coherent
$\mathcal O_{\mathbf P^1_k}$-module. Then there is an exact
sequence of $\mathcal O_{\mathbf P^1_k}$-modules

$$
0\longrightarrow\mathcal E_2\longrightarrow\mathcal E_1
\longrightarrow\mathcal E_0\longrightarrow\mathcal G\longrightarrow0
$$

in which each $\mathcal E_i$ is a finite direct sum of modules
$\mathcal O(d)$, $d\in\mathbf Z$, with the convention of
[def-sc-p1-standard].
(*Source: the graded Hilbert syzygy theorem – the polynomial
ring $S=k[x_0,x_1]$ has graded global dimension two, so every
finitely generated graded $S$-module has a graded free resolution
of length at most two – combined with the description of coherent
modules on $\operatorname{Proj}S$ as $\widetilde M$ for finitely
generated graded $S$-modules; homological algebra; classical, EGA
II, $\S$2, and Hartshorne, *Algebraic Geometry*, II.5.*)

## Proof

By the description quoted in the statement (classical: the
coherent module $\mathcal G$ is $\widetilde M$ for a finitely
generated graded module $M$ over $S=k[x_0,x_1]$), the graded
Hilbert syzygy theorem quoted in the statement gives a graded free
resolution

$$
0\longrightarrow F_2\longrightarrow F_1\longrightarrow F_0
\longrightarrow M\longrightarrow0
$$

with the $F_i$ finite direct sums of graded free modules
$S(d)$; sheafifying (the functor $\widetilde{(-)}$ is exact) and
using $\widetilde{S(d)}=\mathcal O(d)$, the twisted structure
sheaf of [def-sc-p1-standard], which exists by
[lem-sc-p1-twist-exists], gives the displayed exact sequence
with $\mathcal E_i=\widetilde{F_i}$.
