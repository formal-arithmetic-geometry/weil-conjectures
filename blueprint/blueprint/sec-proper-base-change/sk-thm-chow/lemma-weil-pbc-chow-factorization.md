+++
id = "lemma-weil-pbc-chow-factorization"
kind = "lemma"
title = "Chow and projective factorization"
order = 1064
uses = ["def-nagata-final-descended-model", "def-nagata-finite-type-closed-in-fp", "def-nagata-projective-space-base-change", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-proper-base-change", "lem-weil-pbc-proper-composition", "lem-weil-pbc-proper-immersion-closed", "lem-weil-pbc-proper-to-separated", "lemma-nagata-final-descended-model", "lemma-nagata-projective-space-base-change-proper", "prop-nagata-finite-type-closed-in-fp", "thm-chow-lemma"]
+++
Let $f:X\to Y$ be a proper [def-weil-pbc-scheme-conventions] morphism with
$Y$ affine. There exist a proper surjection $\pi:\widetilde X\to X$, an
integer $n\geq0$, and a closed immersion

$$
 i:\widetilde X\hookrightarrow\mathbf P^n_Y
$$

with $f\circ\pi=p\circ i$, where $p:\mathbf P^n_Y\to Y$ is the structure
morphism. No noetherian or finite-presentation hypothesis is imposed on $Y$ or
$f$. The assertion is stable under base change on $Y$: for any morphism
$Y'\to Y$ the pulled-back data are such data for $X\times_YY'\to Y'$.

(For $Y$ noetherian this is also [cor-chow-lemma-proper], which moreover makes
$\pi$ an isomorphism over a dense open subscheme of $X$.)

## Proof

Here $\mathbf P^n_S$ denotes $\mathbf P(\{0,\dots,n\};S)$ of
[def-nagata-projective-space-base-change]. Since it is defined as
$S\times_{\operatorname{Spec}\mathbf Z}\mathbf P^n_{\mathbf Z}$, associativity
of fibre products gives, for every morphism $S'\to S$, a canonical isomorphism
$\mathbf P^n_S\times_SS'=\mathbf P^n_{S'}$ over $S'$; and
$\mathbf P^n_S\to S$ is proper, in particular separated, by
[lemma-nagata-projective-space-base-change-proper]. We also use freely that
proper morphisms, surjective morphisms, immersions and closed immersions are
stable under base change (for properness this is
[lem-weil-pbc-proper-base-change]), and that a closed immersion followed by an
immersion is an immersion.

*Step 1: a separated finitely presented envelope.* The scheme $Y$ is affine,
hence quasi-compact and quasi-separated, and $f$ is separated and of finite
type. By [prop-nagata-finite-type-closed-in-fp] the envelope
$\mathsf{Env}_{\mathrm{fp}}(X/Y)=(X^{\mathrm{fp}},i^{\mathrm{fp}})$ of
[def-nagata-finite-type-closed-in-fp] consists of a separated $Y$-scheme
$g:X^{\mathrm{fp}}\to Y$ of finite presentation and a closed immersion
$i^{\mathrm{fp}}:X\hookrightarrow X^{\mathrm{fp}}$ over $Y$, so
$g\circ i^{\mathrm{fp}}=f$. (The scheme $X^{\mathrm{fp}}$ need not be proper
over $Y$; only $X$ is.)

*Step 2: a noetherian model of the envelope.* Apply the descended model of
[def-nagata-final-descended-model] to the separated finitely presented
morphism $g$. By [lemma-nagata-final-descended-model] this gives a noetherian
scheme $Y_0$ (a member of the noetherian approximation system of $Y$), a
morphism $Y\to Y_0$, a separated morphism of finite presentation
$g_0:X^{\mathrm{fp}}_0\to Y_0$, and an isomorphism of $Y$-schemes

$$
 \epsilon:X^{\mathrm{fp}}_0\times_{Y_0}Y\xrightarrow{\ \sim\ }X^{\mathrm{fp}}.
$$

*Step 3: Chow's lemma on the model.* The morphism $g_0$ is separated and of
finite type over the noetherian scheme $Y_0$, so [thm-chow-lemma] supplies an
integer $n\geq0$, a proper surjective morphism
$\pi_0:X'_0\to X^{\mathrm{fp}}_0$ and an immersion
$i_0:X'_0\to\mathbf P^n_{Y_0}$ of $Y_0$-schemes, i.e.
$g_0\circ\pi_0=p_0\circ i_0$ with $p_0:\mathbf P^n_{Y_0}\to Y_0$.

*Step 4: base change to $Y$.* Put $X'':=X'_0\times_{Y_0}Y$ and let
$\pi'':=\epsilon\circ(\pi_0\times_{Y_0}\operatorname{id}_Y):X''\to
X^{\mathrm{fp}}$ and
$i'':=i_0\times_{Y_0}\operatorname{id}_Y:X''\to\mathbf P^n_{Y_0}\times_{Y_0}Y
=\mathbf P^n_Y$. Then $\pi''$ is proper and surjective, $i''$ is an
immersion, and both are morphisms over $Y$, so that
$g\circ\pi''=p\circ i''$ (base change of the identity of Step 3).

*Step 5: restriction to $X$.* Define $\widetilde X$ as the preimage of the
closed subscheme $X$ under $\pi''$:

$$
 \widetilde X:=X''\times_{X^{\mathrm{fp}}}X,
 \qquad \pi:=\operatorname{pr}_2:\widetilde X\to X,
 \qquad k:=\operatorname{pr}_1:\widetilde X\hookrightarrow X'',
$$

the fibre product being formed with $\pi''$ and $i^{\mathrm{fp}}$. Then $\pi$
is the base change of $\pi''$ along $i^{\mathrm{fp}}$, hence proper and
surjective, and $k$ is the base change of the closed immersion
$i^{\mathrm{fp}}$ along $\pi''$, hence a closed immersion. Set
$i:=i''\circ k:\widetilde X\to\mathbf P^n_Y$, an immersion. It is a morphism
over $Y$ with

$$
 p\circ i=p\circ i''\circ k=g\circ\pi''\circ k
 =g\circ i^{\mathrm{fp}}\circ\pi=f\circ\pi,
$$

using the cartesian square $\pi''\circ k=i^{\mathrm{fp}}\circ\pi$.

*Step 6: $i$ is a closed immersion.* The composite $f\circ\pi$ is proper by
[lem-weil-pbc-proper-composition], since $\pi$ and $f$ are proper. So
$\widetilde X$ is proper over $Y$, and $i$ is a $Y$-morphism to the separated
$Y$-scheme $\mathbf P^n_Y$; by [lem-weil-pbc-proper-to-separated] the morphism
$i$ is proper. A proper immersion is a closed immersion
[lem-weil-pbc-proper-immersion-closed]. Hence $(\pi,n,i)$ has all the required
properties.

*Step 7: base-change stability.* Given such data $(\pi,n,i)$ for $f$ and any
morphism $Y'\to Y$, the base changes
$\pi\times_Y Y':\widetilde X\times_YY'\to X\times_YY'$ and
$i\times_YY':\widetilde X\times_YY'\to\mathbf P^n_Y\times_YY'=\mathbf
P^n_{Y'}$ are a proper surjection and a closed immersion, and the identity
$f\circ\pi=p\circ i$ of morphisms over $Y$ base changes to the corresponding
identity over $Y'$. $\square$

## Remark

The proof never descends $X$ itself: when $f$ is not of finite presentation
no descent $X=X_0\times_{Y_0}Y$ need exist. Only the separated finitely presented
envelope $X^{\mathrm{fp}}$ is descended, Chow's lemma is applied to its
noetherian model, which is merely separated of finite type, and properness of
the resulting closed immersion is recovered on $X$ in Step 6.
