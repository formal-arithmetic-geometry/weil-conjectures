+++
id = "fix-prop-adjunctions"
kind = "theorem"
title = "Adjunctions of the datum"
order = 1872
tags = ["latex:proposition"]
uses = ["def-exchange-projection", "def-fix-six-functor-datum", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-integral-rational-qbar-compact-support", "def-weil-pbc-derived-categories", "def-weil-pbc-inverse-image", "def-weil-pbc-kinjective-resolutions", "fix-lem-exchanges", "lem-weil-derived-direct-image-composition", "lem-weil-derived-tensor-resolution-independent", "thm-sf-comp-composition"]
+++
In the six-functor datum of
[def-fix-six-functor-datum]:

1. the derived pullback and the derived direct image form an
adjoint pair
$$
Lf^*\dashv Rf_*
$$
on $D^b_c(Y,\Lambda)$ and $D^b_c(X,\Lambda)$, with unit
$\eta_f:\operatorname{id}\to Rf_*Lf^*$ and counit
$\varepsilon_f:Lf^*Rf_*\to\operatorname{id}$, satisfying the
triangle identities
$$
(Rf_*\varepsilon_f)\circ(\eta_fRf_*)=\operatorname{id}_{Rf_*},
\qquad
(\varepsilon_fLf^*)\circ(Lf^*\eta_f)=\operatorname{id}_{Lf^*};
$$
1. if $f$ is
exceptionally
admissible, the compact-support direct image and the exceptional
inverse image form an adjoint pair
$$
Rf_!\dashv Rf^!
$$
on $D^b_c(X,\Lambda)$ and $D^b_c(Y,\Lambda)$, with unit
$\nu_f:\operatorname{id}\to Rf^!Rf_!$ and counit
$\mu_f:Rf_!Rf^!\to\operatorname{id}$ satisfying the two triangle
identities; the units and counits agree for the refinement
comparisons, and the adjunction restricts to an adjunction
$$
Rf_!:D^b_{ctf}(X,\Lambda)\rightleftarrows
D^b_{ctf}(Y,\Lambda):Rf^!;
$$
1. for composable separated finite-type morphisms
$X\xrightarrow{f}Y\xrightarrow{g}Z$, the unit of
$L(gf)^*\dashv R(gf)_*$ is the composite
$Lf^*\eta_gLf^*\circ\eta_f$ and the counit is the composite of the
counits; for the exceptional pair the unit and counit of
$R(gf)_!\dashv R(gf)^!$ are the pasted units and counits of
$Rf_!\dashv Rf^!$ and $Rg_!\dashv Rg^!$ under the composition
law of [thm-sf-comp-composition], i.e. the mate of
the composition isomorphism;
1. the adjunction is compatible with the exchange
transformations: the transpose of $\operatorname{Ex}_!$ is
the corresponding exceptional-inverse-image identification, and
$\operatorname{Ex}_*$ is the transpose of the base-change
composite of [def-exchange-projection].

## Proof

Step 1: the derived adjunction $(Lf^*,Rf_*)$. The sheaf-level
adjunction of inverse image and direct image, its derived form
$Lf^*\dashv Rf_*$ on the categories of
[def-weil-pbc-derived-categories], and its unit and counit
$\eta_f,\varepsilon_f$ are [def-weil-pbc-inverse-image] of
the ambient-foundations chapter (finite etale level; the pro-etale level is the site
transport of the same datum, the operations being those of
[def-weil-derived-pullback-tensor-hom] and
[def-weil-derived-direct-image]); the triangle identities hold
for the derived adjunction because the derived unit and counit are
the images of the sheaf-level ones under K-injective and K-flat
replacement of [def-weil-pbc-kinjective-resolutions], the
resolution-independence of
[lem-weil-derived-tensor-resolution-independent], and the sheaf-level
triangle identities are preserved by the derived functors. Step 2:
the exceptional adjunction $(Rf_!,Rf^!)$. The natural adjunction
isomorphisms $\Hom_Y(Rf_!K,L)\cong\Hom_X(K,Rf^!L)$ characterize
$Rf^!$ by [def-weil-exceptional-inverse-image], so the
adjunction $Rf_!\dashv Rf^!$, its unit and counit, and the
triangle identities are the datum of
[def-weil-exceptional-adjoint-admissibility]; the agreement of
the units and the counits with the refinement comparisons is
condition (1) of that definition, and the restriction to the
finite-Tor subcategories is condition (3) of the same definition.
Step 3: composition. The composite adjunction of step 1 is the
paste of the component adjunctions (the unit of the composite is the
composite of the units, the counit the composite of the counits, and
the triangle identities of the composite are the composites of the
triangle identities of the components, through the composition
isomorphisms $R(gf)_*\cong Rg_*Rf_*$ of
[lem-weil-derived-direct-image-composition], which are natural, unital
and associative); for the
exceptional pair, the mate of the composition isomorphism of
[thm-sf-comp-composition] (with its transports of
[def-weil-integral-rational-qbar-compact-support]) gives an
isomorphism $(g\circ f)^!\cong f^!g^!$, the pasted units and
counits are the mates of this isomorphism through the two component
adjunctions, and the triangle identities are the composite versions
of the component ones. Step 4: exchange compatibility. The
transpose of $\operatorname{Ex}_!$ is obtained by the mate
calculus of [def-exchange-projection]: the exchange
transformation is defined as the transpose of the compatibility of
the pullbacks with the counit, and the same holds for
$\operatorname{Ex}_*$; the compatibility of these transposes with
the composition law is [fix-lem-exchanges].
