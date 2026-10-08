+++
id = "lem-chow-graph"
kind = "lemma"
title = "The graph of the cover"
order = 1057
lean = ["AlgebraicGeometry.ChowGraph", "AlgebraicGeometry.ChowGraph.emb", "AlgebraicGeometry.ChowGraph.exists_isClosedImmersion_over", "AlgebraicGeometry.ChowGraph.proj", "AlgebraicGeometry.ChowGraph.toGraph"]
uses = ["def-chow-segre", "def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-comparison", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-affine-immersion", "lem-chow-closed-model", "lem-chow-scheme-theoretic-closure", "lem-chow-segre", "lem-chow-tuple-immersion", "lem-weil-pbc-closed-immersion-products", "lemma-nagata-dense-affine-cover-exists", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal"]
+++
Let $S$ be noetherian, let $X\to S$ be separated of finite type and let
$X=U_1\cup\dots\cup U_m$ be a finite affine open covering such that
$U:=U_1\cap\dots\cap U_m$ is scheme-theoretically dense in $X$. Choose, by
[lem-chow-affine-immersion], immersions
$j_i\colon U_i\to\mathbf P^{n_i}_S$ and, by [lem-chow-closed-model],
closed subschemes $Z_i\subseteq\mathbf P^{n_i}_S$ with $U_i\to Z_i$ a
scheme-theoretically dense open immersion and $Z_i\to S$ proper. Let
$Z\subseteq\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S$ be the
scheme-theoretic image of

$$
j=(j_1|_U,\dots,j_m|_U)\colon U
\longrightarrow\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S .
$$

Then:

1. $Z\to\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S$ is a
closed immersion, $j$ induces an open immersion $U\to Z$ identifying $U$ with
a scheme-theoretically dense open subscheme of $Z$, and $Z\to S$ is proper;
1. for every $i$ the projection $\mathrm{pr}_i|_Z\colon Z\to\mathbf P^{n_i}_S$ factors through $Z_i$, and the induced morphism
$p_i\colon Z\to Z_i$ is proper;
1. $p_i|_U$ is the open immersion $U\to U_i\to Z_i$; in particular
$U\subseteq p_i^{-1}(U_i)$.

The formalisation takes the $m$-fold fibre product
$\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S$ to be the categorical
product in the category of $S$-schemes, so that (1) is a closed immersion into
that product rather than into a single projective space; the composition with
the Segre embedding of [lem-chow-segre], giving a closed immersion
$Z\to\mathbf P^N_S$ over $S$ as used in Step 7 of the proof of
[thm-chow-lemma], is the separate statement
`ChowGraph.exists_isClosedImmersion_over` listed above. It also
weakens the hypotheses to what the proof uses:
the members of the cover need not be affine and need not cover $X$, only $X$
needs to be a noetherian space, and $U$ need not be dense in $X$.

## Proof

Each $j_i|_U$ is an immersion, being the composition of the open immersion
$U\to U_i$ with the immersion $j_i$. Hence $j$ is an immersion by
[lem-chow-tuple-immersion], and it is quasi-compact because $U$ is
noetherian. Part (1) now follows from 01RG for the first two
assertions; for the third, $\mathbf P^{n_1}_S\times_S\dots\times_S \mathbf P^{n_m}_S\to S$ is proper, being a finite fibre product of proper
$S$-schemes, and $Z$ is a closed subscheme of it, so $Z\to S$ is proper by
01W5.

For (2), the open immersion $U\to Z$ is quasi-compact and scheme-theoretically
dominant, so $\mathrm{pr}_i|_Z\colon Z\to\mathbf P^{n_i}_S$ and its restriction
$\mathrm{pr}_i\circ j=j_i|_U$ to $U$ have the same kernel. That kernel
contains the ideal sheaf of $Z_i$, because $j_i|_U$ factors through $Z_i$ by
construction; so the universal property of the closed immersion
$Z_i\to\mathbf P^{n_i}_S$ produces the morphism $p_i\colon Z\to Z_i$ with
$p_i$ followed by $Z_i\to\mathbf P^{n_i}_S$ equal to $\mathrm{pr}_i|_Z$. (This
is 01R9 in the case in which $Z_i$ is presented as the
scheme-theoretic image of $j_i|_U$, which it is: formation of the
scheme-theoretic image commutes with restriction to the open $U_i\subseteq X$.)
It is proper: $Z\to S$ is proper by (1) and $Z_i\to S$ is separated, so $p_i$
is proper by 01W6.

Part (3) is immediate from $\mathrm{pr}_i\circ j=j_i|_U$ and the fact that
$j_i$ identifies $U_i$ with an open subscheme of $Z_i$.

## Detailed form

Let $Y=\operatorname{Spec}A$ be affine, let $X\to Y$ be of finite type, and
let $X=U_1\cup\dots\cup U_m$ be the affine open cover of
[lemma-nagata-dense-affine-cover-exists], with its dense open $U:=\bigcap_iU_i$.
Applying [lem-chow-scheme-theoretic-closure] (which keeps $X$ proper
if it was, and keeps each $U_i$ affine and of finite type over $Y$), we assume
from now on that $U$ is scheme-theoretically dense in $X$. For each $i$, let
$U_i\hookrightarrow\mathbf P^{n_i}_Y$ be the immersion of
[lem-chow-affine-immersion], and let
$Z_i\subseteq\mathbf P^{n_i}_Y$ be the closed model of
[lem-chow-closed-model], so that $U_i\hookrightarrow Z_i$ is a
scheme-theoretically dense open immersion. Put

$$
 Z:=\prod_{i=1}^mZ_i,
$$

and let $\widetilde X\subseteq Z$ be the scheme-theoretic image
([def-nagata-scheme-theoretic-image]) of the diagonal morphism

$$
 j=(j_1|_U,\dots,j_m|_U):U\longrightarrow Z.
$$

Then:

- (i) $U\hookrightarrow\widetilde X$ is a scheme-theoretically dense open
  immersion, and $\widetilde X\to Y$ is proper;
- (ii) the projections $\mathrm{pr}_i|_{\widetilde X}:\widetilde
  X\to\mathbf P^{n_i}_Y$ factor through $Z_i$, i.e. there are morphisms
  $p_i:\widetilde X\to Z_i$ with
  $p_i=(\mathrm{pr}_i|_{\widetilde X}\text{ co-restricted})$, and each $p_i$
  is proper;
- (iii) the composite

  $$
   \widetilde X\hookrightarrow Z\hookrightarrow\prod_{i=1}^m\mathbf P^{n_i}_Y
   \xrightarrow{\ s\ }\mathbf P^N_Y,\qquad N=\prod_{i=1}^m(n_i+1)-1,
  $$

  of the closed immersion $\widetilde X\hookrightarrow Z$, the product of the
  closed immersions $Z_i\hookrightarrow\mathbf P^{n_i}_Y$, and the Segre
  embedding ([def-chow-segre],
  [lem-chow-segre]) is a closed immersion.

## Proof

*The reduction step is legitimate.* By
[lem-chow-scheme-theoretic-closure], $X^{*}\to X$ is a surjective
closed immersion and $U\subseteq X^{*}$ is scheme-theoretically dense;
$\pi:X^{*}\to X$ is proper whenever $X\to Y$ is (a closed immersion followed
by a proper morphism is proper), so conclusions about properness pass from
$X^{*}$ to $X$, and the $U_i^{*}=X^{*}\cap U_i$ are affine, of finite type
over $Y$, with $U=\bigcap_iU_i^{*}$. Hence we may replace $X$ by $X^{*}$ and
$U_i$ by $U_i^{*}$.

*$j$ is an immersion.* By [lem-chow-affine-immersion] each
$j_i|_U$ factors as the closed immersion $U\hookrightarrow\mathbf A^{n_i}_Y$
followed by the open immersion $\mathbf A^{n_i}_Y\hookrightarrow\mathbf
P^{n_i}_Y$. The induced morphism $U\to\prod_i\mathbf A^{n_i}_Y$ is a closed
immersion: the target is affine with coordinate ring the tensor product over
$A$ of the coordinate rings of the $\mathbf A^{n_i}_Y$, and each of the
coordinate ring maps onto $B=\mathcal O_U(U)$ is surjective, hence so is the
tensor product map. Composing with the open immersion $\prod_i\mathbf
A^{n_i}_Y\hookrightarrow\prod_i\mathbf P^{n_i}_Y$ and using that
$\prod_iZ_i\subseteq\prod_i\mathbf P^{n_i}_Y$ is closed, we get that $j:U\to
Z$ is an immersion.

*Proof of (i).* Stacks Project, Morphisms, Lemma 29.7.7 (Tag
[01RG](https://stacks.math.columbia.edu/tag/01RG)) applied to the
quasi-compact immersion $j$ (its source $U$ is quasi-compact) shows that the
scheme-theoretic image $\widetilde X$ of $j$ contains $U$ as a
scheme-theoretically dense open subscheme. For properness: each $Z_i\to Y$ is
proper by [lem-chow-closed-model]; $Z=\prod_iZ_i$ is closed in
$\prod_i\mathbf P^{n_i}_Y$ (a product of closed immersions is a closed
immersion), and $\prod_i\mathbf P^{n_i}_Y$ is proper over $Y$ by
[lem-chow-segre] and
[def-chow-segre] (its structure morphism is the composite
of the closed Segre immersion $\prod_i\mathbf P^{n_i}_Y\hookrightarrow\mathbf
P^N_Y$ with the proper $\mathbf P^N_Y\to Y$); hence $Z\to Y$ is proper, and
the closed subscheme $\widetilde X\subseteq Z$ is proper over $Y$ too
(`closed subscheme` means the composite of the closed immersion with the
proper morphism is proper).

*Proof of (ii).* The morphism $\mathrm{pr}_i\circ j$ equals $j_i|_U:\ U\to
Z_i\subseteq\mathbf P^{n_i}_Y$, i.e. it factors through the closed subscheme
$Z_i$; by the universal property of the scheme-theoretic image
([def-nagata-scheme-theoretic-image]; equivalently Stacks Project,
Morphisms, Lemma 29.6.6, Tag
[01R9](https://stacks.math.columbia.edu/tag/01R9)), the induced morphism
$\mathrm{pr}_i|_{\widetilde X}:\widetilde X\to\mathbf P^{n_i}_Y$ thus factors
through $Z_i$, giving $p_i$. The morphism $p_i$ is proper by Stacks Project,
Morphisms, Lemma 29.42.7 (Tag
[01W6](https://stacks.math.columbia.edu/tag/01W6)): $\widetilde X\to Y$ is
proper by (i), the target $Z_i$ is separated over $Y$ (it is a closed
subscheme of the projective $Y$-scheme $\mathbf P^{n_i}_Y$, which is separated
over $Y$), and a morphism from a $Y$-proper scheme to a $Y$-separated scheme
is proper.

*Proof of (iii).* $\widetilde X\hookrightarrow Z$ is a closed immersion by the
definition of the scheme-theoretic image
([def-nagata-scheme-theoretic-image]); the product of the closed
immersions $Z_i\hookrightarrow\mathbf P^{n_i}_Y$ is a closed immersion; and
$s$ is a closed immersion by [lem-chow-segre].
Compositions of closed immersions are closed immersions, which proves (iii).
