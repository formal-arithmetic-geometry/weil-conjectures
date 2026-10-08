+++
id = "lem-fin-finite-splitting"
kind = "lemma"
title = "Etale splitting of a finite morphism"
order = 996
uses = ["def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit"]
+++
Let $f:X\to S$ be a finite
morphism, and let $\bar s$ be a
geometric point of $S$.
There are a pointed etale neighborhood $V\to S$ of $\bar s$ and a
decomposition

$$
X\times_SV=X_1\sqcup\cdots\sqcup X_m
$$

into open-and-closed $V$-subschemes, with $m$ the number of geometric
points of the finite fibre $X_{\bar s}$, such that every $X_i\to V$ is
finite and the geometric fibre $(X_i)_{\bar v}$ over the lifted point
$\bar v$ of $V$ is connected.

## Proof

The morphism $f$ is finite in the sense of
[def-weil-pbc-scheme-conventions], hence affine; replacing $S$ by an
affine open through which $\bar s$ factors we may assume
$S=\operatorname{Spec}R$ and $X=\operatorname{Spec}C$ with $C$ a
finite $R$-algebra. Let $A=\mathcal O^{{\mathrm{sh}}}_{S,\bar s}$ be
the strict henselization of [def-weil-pbc-strict-henselization-limit],
the filtered colimit of the rings $A_V$ of the affine pointed etale
neighbourhoods $(V,\bar v)$ of $\bar s$. The scheme
$X\times_S\operatorname{Spec}A$ is the spectrum of the finite
$A$-algebra $B=C\otimes_RA=\varinjlim_V C\otimes_RA_V$. The ring $A$
is strictly henselian local (Stacks Project, Algebra, Lemma 10.155.10,
Tag [04GQ](https://stacks.math.columbia.edu/tag/04GQ)), so the finite
$A$-algebra $B$ is a finite product $B=B_1\times\cdots\times B_m$ of
local rings (Algebra, Lemma 10.153.3 (10), Tag
[04GG](https://stacks.math.columbia.edu/tag/04GG)). The residue field
of each $B_i$ is finite over the separably closed residue field of $A$,
hence purely inseparable over it, so each factor contributes exactly
one geometric point to the finite fibre $X_{\bar s}$ in the sense of
[def-weil-pbc-geometric-stalks]; thus $m$ is the number of geometric
points of $X_{\bar s}$.

Let $e_1,\dots,e_m\in B$ be the factor idempotents. Each comes from
$C\otimes_RA_V$ for some $V$, and the finitely many relations
$e_i^2=e_i$, $e_ie_j=0$ for $i\ne j$ and $\sum_ie_i=1$ hold after
passing to a further neighbourhood, since $B$ is the filtered colimit of
the $C\otimes_RA_V$. Over such a $V$ the idempotents decompose
$X\times_SV=\operatorname{Spec}(C\otimes_RA_V)$ as
$X_1\sqcup\cdots\sqcup X_m$ into open-and-closed subschemes, each
$X_i\to V$ is finite (a closed subscheme of the finite $V$-scheme
$X\times_SV$), and the geometric fibre $(X_i)_{\bar v}$ is the single
geometric point contributed by $B_i$, hence connected.
