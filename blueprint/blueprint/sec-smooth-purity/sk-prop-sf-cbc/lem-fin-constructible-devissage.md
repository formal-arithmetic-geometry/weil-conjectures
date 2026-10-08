+++
id = "lem-fin-constructible-devissage"
kind = "lemma"
title = "Devissage of a constructible sheaf"
order = 1524
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-extension-by-zero", "lemma-weil-pbc-geometric-stalk-conservative", "sbc-def-coefficient-conventions"]
+++
Let $X$ be of finite type over $k$ and let $F$ be a
constructible
$\Lambda$-sheaf on $X_{{\mathrm{et}}}$. There is a finite filtration
by subsheaves

$$
0=F_0\subset F_1\subset\cdots\subset F_m=F
$$

and locally closed constructible subschemes
$j_r:X_r\hookrightarrow X$, with
lisse
$\Lambda$-sheaves $L_r$ on $(X_r)_{{\mathrm{et}}}$, such that

$$
F_r/F_{r-1}\cong(j_r)_!L_r\qquad(1\leq r\leq m).
$$

Here $(j_r)_!$ is the extension by zero of
[def-weil-pbc-extension-by-zero] along the locally closed
immersion. The filtration need not split.

## Proof

Choose a finite stratification on which $F$ is lisse, as in
[def-weil-pbc-constructible-complexes]. A finite refinement of
this stratification has the frontier property: the closure of each
stratum is a union of strata. To construct such a refinement, choose
disjoint dense open subsets of the finitely many irreducible
components, small enough to lie in the original strata, and repeat
on their closed complement. Dimension decreases on the complement,
so this process terminates. In particular there is a dense open
$j:U\hookrightarrow X$ on which $F$ is lisse, with closed complement
$i:Z\hookrightarrow X$ of smaller dimension.

The adjunction maps give a short exact sequence

$$
0\longrightarrow j_!j^*F\longrightarrow F
\longrightarrow i_*i^*F\longrightarrow0.
$$

Indeed, the stalk descriptions of
[def-weil-pbc-extension-by-zero] identify this sequence at a
point of $U$ with $0\to F_{\bar x}\to F_{\bar x}\to0$, and at a
point of $Z$ with $0\to0\to F_{\bar x}\to F_{\bar x}\to0$.
Exactness follows from the conservativity and exactness of geometric
stalks in [lemma-weil-pbc-geometric-stalk-conservative].
Induct on dimension for the constructible restriction $i^*F$ on
$Z$. The functor $i_*$ is exact by the same stalk description.
Push its finite filtration to $X$, take its inverse images under
$F\twoheadrightarrow i_*i^*F$, and prepend $j_!j^*F$.
The resulting subquotients are extensions by zero from the locally
closed strata of $X$, as required. The empty scheme starts the
induction.
