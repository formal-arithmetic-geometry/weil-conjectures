+++
id = "thm-fin-open-degree-zero"
kind = "theorem"
title = "Constructibility of the degree-zero open direct image"
order = 1909
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-closed-immersion", "lem-fin-dense-normal-open", "lem-fin-normal-open-lisse-image", "lem-weil-pbc-constructible-subobjects-noetherian", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-finite-stalk-formula", "lemma-weil-pbc-geometric-stalk-conservative", "thm-constructible-serre", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $X$ be of finite type over a field, let
$j:U\hookrightarrow X$ be an
open immersion,
and let $F$ be a
constructible
module sheaf over a finite commutative ring on $U_{\Et}$.
Then $j_*F$ is
constructible on $X_{\Et}$.

## Proof

We prove the assertion for every open in $X$ by Noetherian
induction on the ambient closed subset. Reduction of the
ambient scheme causes no change, by
[thm-weil-pbc-universal-homeomorphism-invariance].
The inverse-image equivalences for reduction commute with
open restriction; adjunction then identifies their direct
images as well. Thus take $X$ reduced.
If $U$ is not dense, factor it through the proper closed
subset $\overline U$, use induction there, and use
[lem-fin-closed-immersion] to push to $X$.

Suppose $U$ is dense. There are finitely many irreducible
components $X_a$, by
[lem-weil-pbc-noetherian-finite-components]. The finite
partition of $F$ in
[def-weil-pbc-constructible-complexes] contains a lisse
open near each generic point. Inside it choose a normal
nonempty open $V_a\subset X_a$, using
[lem-fin-dense-normal-open], and remove all other
components. Each $V_a$ is then open in $X$, lies in
$U$, and the $V_a$'s are disjoint. Put
$V=\coprod V_a$, $h:V\hookrightarrow U$, $k=jh$,
and $L=h^*F$. For each component,
[lem-fin-normal-open-lisse-image] gives a constructible
direct image on $X_a$; then
[lem-fin-closed-immersion] and the finite product give
constructibility of $k_*L$ on $X$.

Let $K=\ker(F\to h_*L)$. This subsheaf of $F$ is
constructible by
[lem-weil-pbc-constructible-subobjects-noetherian],
and its restriction to $V$ is zero. Put $W=X\setminus V$,
$W_U=W\cap U$, with immersions $i:W\hookrightarrow X$,
$i':W_U\hookrightarrow U$, and $j_W:W_U\hookrightarrow W$.
The closed unit identifies $K=i'_*K'$, where
$K'=i'^*K$: this is an isomorphism on all stalks by
[lemma-weil-pbc-finite-stalk-formula] and hence by
[lemma-weil-pbc-geometric-stalk-conservative].
Direct-image composition in
[def-weil-pbc-direct-image] gives
$j_*K=i_*j_{W,*}K'$. Since $W$ is a proper closed
subset, induction and [lem-fin-closed-immersion] make
this sheaf constructible.

Left exactness identifies the kernel of
$j_*F\to j_*h_*L=k_*L$ with $j_*K$.
Its image $I$, being a subsheaf of the constructible
$k_*L$, is constructible by
[lem-weil-pbc-constructible-subobjects-noetherian].
Finally the short exact sequence

$$
0\longrightarrow j_*K\longrightarrow j_*F
\longrightarrow I\longrightarrow0
$$

and [thm-constructible-serre] prove the claim.
This argument uses only the left exactness of $j_*$.
