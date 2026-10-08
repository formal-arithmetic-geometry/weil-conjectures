+++
id = "prop-exc-base-change-proper"
kind = "theorem"
title = "Base change for a proper morphism, against an open immersion"
order = 1814
tags = ["latex:proposition"]
uses = ["cor-sf-ambient-adjoint-discharge", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-pbc-derived-categories", "lem-compact-support-direct-image-triangulated", "lem-exc-closed-support-triangle", "lem-exc-open-fully-faithful", "prop-exc-ambient-dual-base-change"]
+++
Let $f:X\to Y$ be proper, carrying the ambient exceptional right adjoint
datum of [def-weil-ambient-exceptional-adjoint], let
$g:Y'\hookrightarrow Y$ be an open immersion with closed complement
$i:Z\hookrightarrow Y$, and form the Cartesian squares with
$X'=f^{-1}(Y')$, $g':X'\hookrightarrow X$, $f'=f|_{X'}$ and
$i':f^{-1}(Z)\hookrightarrow X$. Then for every object $K$ the
base-change comparison

$$
\beta:\ Lg'^*Rf^{\times}K\xrightarrow{\ \sim\ }Rf'^{\times}Lg^*K
$$

is an isomorphism. On the blueprint's coefficient class
[def-sf-fullcd-used-class] the ambient datum displayed as the hypothesis
is the theorem [cor-sf-ambient-adjoint-discharge], and the argument below
is object-wise, so on that class the comparison is an isomorphism for every
$K$ of the class without hypothesis; the datum is retained for the complexes
outside it, [rem-sf-class-adjoint-residue].

## Proof

Step 1: the target triangle. The closed-support triangle of
[lem-exc-closed-support-triangle] for the pair $(i,g)$ on $Y$ is

$$
i_*Ri^!K\longrightarrow K\longrightarrow Rg_*Lg^*K\xrightarrow{+1}.
$$

Step 2: applying the exact right adjoint. The compact-support direct
image is exact by [lem-compact-support-direct-image-triangulated]; a right adjoint of an exact functor
is exact, so $Rf^{\times}$ carries the triangle into

$$
Rf^{\times}i_*Ri^!K\longrightarrow Rf^{\times}K
\longrightarrow Rf^{\times}Rg_*Lg^*K\xrightarrow{+1}.
$$

Step 3: dual base change in the two squares. The dual base-change
isomorphism [prop-exc-ambient-dual-base-change], applied to the
Cartesian squares of $i$ and of $g$ along $f$, identifies the outer
terms with

$$
i'_*Rf^{\times}_{Z}Ri^!K,
\qquad
Rg'_*Rf'^{\times}Lg^*K,
$$

where $f_Z:f^{-1}(Z)\to Z$ is the restriction of $f$.
Step 4: restriction to the open. Apply $Lg'^*$ to the resulting
triangle. By [lem-exc-open-fully-faithful] the first term is killed
($Lg'^*i'_*=0$, the images of $g'$ and $i'$ being complementary)
and the last term becomes $Rf'^{\times}Lg^*K$
($Lg'^*Rg'_*\cong\operatorname{id}$). A distinguished triangle whose
first term vanishes exhibits its second-to-third map as an isomorphism;
that map is $Lg'^*Rf^{\times}K\to Rf'^{\times}Lg^*K$, the pullback of the
restriction map of the triangle, which is the base-change comparison
$\beta$ (its adjoint under $Rf'_!\dashv Rf'^{\times}$ is the composite
with the counit). Hence $\beta$ is an isomorphism.
