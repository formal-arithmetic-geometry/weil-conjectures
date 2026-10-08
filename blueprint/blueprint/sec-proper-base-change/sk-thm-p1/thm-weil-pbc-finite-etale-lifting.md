+++
id = "thm-weil-pbc-finite-etale-lifting"
kind = "theorem"
title = "Finite-etale lifting over a proper henselian pair"
order = 1138
uses = ["def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "thm-weil-pbc-henselian-idempotent-lifting"]
+++
Let $(A,I)$ be henselian, let $Y\to\operatorname{Spec}A$ be proper, and let
$Y_0=Y\times_AA/I$. Restriction is an equivalence

$$
 \mathsf{FEt}(Y)\xrightarrow{\sim}\mathsf{FEt}(Y_0).
$$

It lifts morphisms and finite group actions uniquely.

**Status.** The former proof invoked the torsion degree-zero comparison for
the map $H^0(Z,\mathcal O_Z)\to H^0(Z_0,\mathcal O_{Z_0})$ on structure
sheaves; that citation applies in neither reading, since the structure sheaf
is not torsion and the two sheaves are different objects. The needed statement
is the idempotent lifting interface
[thm-weil-pbc-henselian-idempotent-lifting], which the proof now cites. The
rest of the proof — properness of $Z$ over $S$, the dictionary between
$Y$-morphisms $Y\to Z$ and rank-one idempotents, the Hom-computation, and
uniqueness of the lifted group action — is proved here and depends on no
further input.

## Proof

Put $S=\operatorname{Spec}A$ and $S_0=\operatorname{Spec}(A/I)$, so
$Y_0=Y\times_SS_0$. For a finite etale $Z\to Y$ the composite $Z\to S$ is
proper: $Z\to Y$ is finite, hence proper, and $Y\to S$ is proper by
hypothesis, so composition applies. Let $\pi:Z\to Y$ be finite etale. The
$Y$-morphisms $Y\to Z$ are the inclusions of a member of a decomposition
$Z=Z_e\amalg Z_{1-e}$ into open and closed $Y$-subschemes, i.e. the
idempotents $e$ of $H^0(Z,O_Z)$ whose piece $Z_e$ has rank one (an affine
finite etale algebra is a product of finite etale pieces, and a piece of rank
one is $Y$-isomorphic to $Y$); here $O_Z$ is the structure sheaf of $Z$, an
etale abelian ring sheaf, and $H^0(Z,O_Z)=\Gamma(Y,\pi_*O_Z)$. By
[thm-weil-pbc-henselian-idempotent-lifting], the idempotent-lifting interface
for the structure sheaf of a proper scheme over a henselian pair applied to
the proper $Z\to S$, restriction induces a bijection between the idempotents
of $H^0(Z,O_Z)$ and those of $H^0(Z_0,O_{Z_0})$, and it matches the open and
closed subschemes of $Z$ with those of $Z_0$: an idempotent $e$ cuts out the
clopen $Z_e\subseteq Z$, and its image cuts out $Z_{0,e_0}=(Z_e)_0$. The
condition that $Z_e$ have rank one over $Y$ is therefore equivalent to the
same condition for $(Z_e)_0$ over $Y_0$: the rank of the finite locally free
$\mathcal O_Y$-module $\pi_*O_{Z_e}$ is locally constant on $Y$, and $Y_0\to
Y$ is surjective, so it is determined by its values on the image of $Y_0$,
which are the ranks of $(Z_e)_0$. This is not the torsion-sheaf comparison,
whose hypothesis of torsion coefficients the structure sheaf does not satisfy,
and it is the object-level half of the finite-etale lifting recorded as Tags
0A0C and 0A3S; the map on idempotents is restriction, hence multiplicative,
and it transports the decompositions, so

$$
 Z(Y)\xrightarrow{\sim}Z_0(Y_0),
$$

natural in $Z$. For finite etale $X,W\to Y$, the set
$\operatorname{Hom}_Y(X,W)$ is $(W\times_YX)(X)$, and
$(W\times_YX)_0=W_0\times_{Y_0}X_0$, the former scheme being finite etale and
proper over $S$; therefore

$$
 \operatorname{Hom}_Y(X,W)\xrightarrow{\sim}
 \operatorname{Hom}_{Y_0}(X_0,W_0),
$$

by restriction. The restriction functor $\mathsf{FEt}(Y)\to\mathsf{FEt}(Y_0)$
is thus fully faithful and lifts morphisms uniquely: a morphism $f_0:V_0\to
W_0$ is the restriction of a unique $f:V\to W$, and a finite group action on
$W_0$ lifts by lifting the automorphisms of its generating set and using
uniqueness for the group relations. Every finite etale $Y_0$-scheme is the
restriction of a finite etale $Y$-scheme, the lifting input of the
henselian-pair proper-base-change package (Stacks Project, Section 59.91: Tag
[0A0C](https://stacks.math.columbia.edu/tag/0A0C) and Tag
[0A3S](https://stacks.math.columbia.edu/tag/0A3S)), so restriction is onto the
object set and the three assertions hold.
