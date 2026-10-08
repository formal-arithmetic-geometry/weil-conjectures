+++
id = "thm-chow-lemma"
kind = "theorem"
title = "Chow's lemma"
order = 1061
lean = ["AlgebraicGeometry.ChowModification", "AlgebraicGeometry.ChowModification.exists_dense_isIso_restrict", "AlgebraicGeometry.ChowModification.index", "AlgebraicGeometry.ChowModification.isImmersion_toProjectiveSpace", "AlgebraicGeometry.ChowModification.isProper_modificationMap", "AlgebraicGeometry.ChowModification.modificationMap", "AlgebraicGeometry.ChowModification.surjective_modificationMap", "AlgebraicGeometry.ChowModification.toProjectiveSpace", "AlgebraicGeometry.ChowModification.toProjectiveSpace_over"]
uses = ["def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-agree-on-dense-open", "lem-chow-closed-model", "lem-chow-glue", "lem-chow-graph", "lem-chow-preimage", "lem-chow-scheme-theoretic-closure", "lem-chow-segre", "lem-chow-tuple-immersion", "lem-weil-pbc-proper-closed-image", "lem-weil-pbc-proper-composition", "lem-weil-pbc-proper-immersion-closed", "lemma-nagata-dense-affine-cover-exists", "lemma-nagata-dense-flat-pullback", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-projective-space-base-change-proper", "lemma-nagata-projective-target-local", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $S$ be a noetherian scheme and let $f\colon X\to S$ be a separated morphism
of finite type. Then there are an integer $n\geq0$, a scheme $X'$ over $S$, a
morphism $\pi\colon X'\to X$ and an immersion $i\colon X'\to\mathbf P^n_S$ of
$S$-schemes such that

1. $\pi$ is proper and surjective, and
1. there is a dense open subscheme $U\subseteq X$ such that
$\pi^{-1}(U)\to U$ is an isomorphism.

The formalisation makes $X'$, the index set of the homogeneous coordinates of
the ambient projective space, $\pi$ and $i$ four separate definitions rather
than existentially bound data, so that a consumer gets properness, surjectivity
and the immersion property by typeclass inference; all four are read off a
single auxiliary choice, `ChowModification.data`. Following
[def-nagata-projective-space-base-change], $\mathbf P^n_S$ is
$\mathbf P(N;S)$ for a finite type $N$ of homogeneous coordinates. Finally,
[lem-chow-graph] needs the covering of Step 1 to be nonempty; this costs
nothing, since $m=0$ happens only for $X$ empty, and one may then replace the
covering by the one-element covering $\{X^{*}\}$.

## Proof

By the scheme conventions [def-weil-pbc-scheme-conventions] (Stacks 01T6, 0BA8, 01T8, 01KV) the scheme $X$ is
noetherian and has finitely many irreducible components, and it is
quasi-compact and quasi-separated.

*Step 1: the cover.* By [lemma-nagata-dense-affine-cover-exists] there is a finite
affine open covering $X=U_1\cup\dots\cup U_m$ whose members all contain the
generic points of the irreducible components of $X$, and
$U:=U_1\cap\dots\cap U_m$ is a dense open subscheme of $X$.

*Step 2: reduction to $U$ scheme-theoretically dense.* Let
$X^{*}\subseteq X$ be the scheme-theoretic image of $U\to X$, as in
[lem-chow-scheme-theoretic-closure]. Then $X^{*}\to S$ is again separated
of finite type, $X^{*}=\bigcup_iU_i^{*}$ is a finite affine open covering with
$\bigcap_iU_i^{*}=U$, and $U$ is scheme-theoretically dense in $X^{*}$.
It suffices to produce, for $X^{*}$ with the covering $\{U_i^{*}\}$ and the
same open $U$, a proper surjective morphism $\pi^{*}\colon X'\to X^{*}$ and an
immersion $X'\to\mathbf P^n_S$ such that $(\pi^{*})^{-1}(U)\to U$ is an
isomorphism; this is exactly what Steps 3–7 below construct. Indeed,
$X^{*}\to X$ is a surjective closed immersion, hence proper and surjective, and
it is an isomorphism over $U$; so $\pi:=(X^{*}\to X)\circ\pi^{*}$ is proper and
surjective, $U$ is a dense open subscheme of $X$, and
$\pi^{-1}(U)=(\pi^{*})^{-1}(U)\to U$ is an isomorphism. We may therefore
replace $X$ by $X^{*}$ and $U_i$ by $U_i^{*}$, and assume from now on that $U$
is scheme-theoretically dense in $X$.

*Step 3: the graph.* Apply [lem-chow-graph] to obtain immersions
$j_i\colon U_i\to\mathbf P^{n_i}_S$, their closed models $Z_i$, the
scheme-theoretic image $Z$ of $j=(j_1|_U,\dots,j_m|_U)$, the proper
projections $p_i\colon Z\to Z_i$, and the closed immersion
$Z\to\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S$.

*Step 4: the modification.* Put $V_i:=p_i^{-1}(U_i)$ and
$X':=V_1\cup\dots\cup V_m$. By [lem-chow-glue] the morphisms
$p_i|_{V_i}$ glue to $\pi\colon X'\to X$ with $\pi|_U=\mathrm{id}_U$, and by
[lem-chow-preimage] we have $\pi^{-1}(U_i)=V_i$ with
$\pi^{-1}(U_i)\to U_i$ proper.

*Step 5: $\pi$ is proper and surjective.* Properness is local on the
target by 01W2, and $X=\bigcup_iU_i$ is an open covering with
$\pi^{-1}(U_i)\to U_i$ proper; hence $\pi$ is proper. In particular
$\pi(X')\subseteq X$ is closed. It contains $U$ because
$\pi|_U=\mathrm{id}_U$, and $U$ is dense in $X$; therefore $\pi(X')=X$.

*Step 6: $\pi$ is an isomorphism over $U$.* Repeat the argument of
[lem-chow-preimage] with $U_i$ replaced by $U$: the identity
$U\to U$ is proper, $\pi^{-1}(U)\to U$ is separated, so
01W6 shows that $U\to\pi^{-1}(U)$ is universally closed and
hence $U$ is closed in $\pi^{-1}(U)$; and $U$ is dense in the open subscheme
$\pi^{-1}(U)\subseteq Z$. Thus $U=\pi^{-1}(U)$ and $\pi^{-1}(U)\to U$ is the
identity.

*Step 7: the immersion.* Put $N=\prod_i(n_i+1)-1$. Composing the closed
immersion $Z\to\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S$ of
[lem-chow-graph](1) with the Segre embedding, which is a closed
immersion by [lem-chow-segre], gives a closed immersion
$Z\to\mathbf P^N_S$. The subscheme $X'\subseteq Z$ is open, so the composition
$i\colon X'\to\mathbf P^N_S$ is an immersion. Taking $n:=N$ completes the
proof.

## Detailed form

In the situation of [lem-chow-glue], the morphism
$\pi:X'\to X$ is proper and surjective, and

$$
 \pi^{-1}(U)\xrightarrow{\sim}U
$$

is an isomorphism.

## Proof

*Properness of $\pi$.* By [lem-chow-preimage] the
restrictions $\pi^{-1}(U_i)\to U_i$ are proper for every member of the finite
affine open cover $X=U_1\cup\dots\cup U_m$. Properness is local on the target
(Stacks Project, Morphisms, Lemma 29.42.3, Tag
[01W2](https://stacks.math.columbia.edu/tag/01W2): a morphism $g:W\to S$ is
proper as soon as there is an open cover $S=\bigcup_jS_j$ with
$g^{-1}(S_j)\to S_j$ proper for all $j$); applying this to $g=\pi$, $S=X$,
$S_j=U_j$ shows that $\pi$ is proper.

*Surjectivity of $\pi$.* A proper morphism has closed image (Stacks Project,
Morphisms, Lemma 29.42.7, Tag
[01W6](https://stacks.math.columbia.edu/tag/01W6)). Hence $\pi(X')\subseteq X$
is closed; it contains $U$ (since $\pi|_U=\operatorname{id}_U$ by
[lem-chow-glue]), and $U$ is dense in $X$ (it is
scheme-theoretically dense after the reduction of
[lem-chow-graph], hence topologically dense). Thus
$\pi(X')=X$, i.e. $\pi$ is surjective.

*The isomorphism over $U$.* Identify $U$ with an open subscheme of
$\pi^{-1}(U)\subseteq X'$ via the inclusion of the dense open. We apply Stacks
Project, Morphisms, Lemma 29.42.7 (Tag
[01W6](https://stacks.math.columbia.edu/tag/01W6)) to the diagram whose
composite $U\to\pi^{-1}(U)\to U$ is the identity (hence proper) and whose
second member $\pi^{-1}(U)\to U$ is separated over $U$ (the morphism
$\pi^{-1}(U)\to U$ is the base change of the separated morphism $\pi$, see the
first step of the proof of [lem-chow-preimage]): the
lemma yields that $U\to\pi^{-1}(U)$ is proper, hence closed, so $U$ is closed
in $\pi^{-1}(U)$. On the other hand $U$ is scheme-theoretically dense in
$\widetilde X$ by [lem-chow-graph] (i), and
$\pi^{-1}(U)\subseteq\widetilde X$ is open, so $U$ is dense in $\pi^{-1}(U)$.
A closed and dense subscheme of a scheme coincides with it: $U=\pi^{-1}(U)$
inside $X'$, and $\pi^{-1}(U)\to U$ is the isomorphism inverse to the
inclusion.

*The closed immersion $i$.* The composed morphism $i$ is an immersion:
$X'\subseteq\widetilde X$ is open ($X'=\bigcup_iV_i$ with the
$V_i\subseteq\widetilde X$ open), and the remaining factors are closed
immersions by [lem-chow-graph] (iii) and
[lem-chow-segre]; a composite of an open immersion
and closed immersions is an immersion. Its source is proper over $Y$: $\pi$ is
proper by the first paragraph and $f:X\to Y$ is proper by hypothesis, so
$f\circ\pi:X'\to Y$ is the composite of two proper morphisms, hence proper. By
Tag [01W6](https://stacks.math.columbia.edu/tag/01W6) once more, now with
$X=X'$, $S=Y$, $Y'=\mathbf P^N_Y$ (separated over $Y$, being projective), the
morphism $X'\to\mathbf P^N_Y=i$ is proper. A proper immersion is a closed
immersion (Stacks Project, Schemes, Lemma 26.10.4, Tag
[01IQ](https://stacks.math.columbia.edu/tag/01IQ): an immersion is a closed
immersion iff its image is closed; here the image is closed by properness, Tag
[01W6](https://stacks.math.columbia.edu/tag/01W6)). Hence $i$ is a closed
immersion.

*The factorization.* Both $f\circ\pi$ and the composite $X'\xrightarrow{i}
\mathbf P^N_Y\to Y$ are equal to the structure morphism of the $Y$-scheme
$X'$: all schemes involved are defined over $Y$ and every morphism displayed
is a morphism over $Y$ (the open immersions $V_i\subseteq\widetilde X$, the
closed immersions and the projections $p_i$ are all over $Y$, and $\pi$ is a
morphism of $Y$-schemes by [lem-chow-glue]). Hence
$f\circ\pi=p\circ i$ with $p:\mathbf P^N_Y\to Y$.
