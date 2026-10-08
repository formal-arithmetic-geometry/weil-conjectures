+++
id = "lemma-nagata-admissible-blowup-preserves-density"
kind = "lemma"
title = "Density is preserved by an admissible blow-up"
order = 103
lean = ["AlgebraicGeometry.IsAdmissible.isSchemeTheoreticallyDominant_preimage_ι", "AlgebraicGeometry.Scheme.IdealSheafData.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support"]
uses = ["def-nagata-admissible-blowup", "def-nagata-dense-compactification", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "def-nagata-scheme-theoretically-dense-open", "lemma-nagata-dense-flat-pullback", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-global-blowup-complement"]
+++
Let $U\hookrightarrow X$ be a quasi-compact scheme-theoretically dense open
immersion, and let $\mathcal I$ be a finite type quasi-coherent ideal with
$\mathcal I|_U=\mathcal O_U$. Then the inverse image of $U$ is
scheme-theoretically dense in $\operatorname{Bl}_{\mathcal I}(X)$.
Consequently the same assertion holds after any finite composite of
$U$-admissible blow-ups.

## Proof

First, the complement of the support of an invertible ideal is
scheme-theoretically dense: on an affine open where the ideal is generated
by a single non-zero-divisor $a$, the restriction map to the complement of
the support is the localization away from $a$, which is injective.
Applying this on $\operatorname{Bl}_{\mathcal I}(X)$ to the extended ideal
$\mathcal I\mathcal O_{\operatorname{Bl}_{\mathcal I}(X)}$, which is
invertible by [thm-nagata-blowup-principalizes-center], shows that the
inverse image of the complement $W$ of the center is scheme-theoretically
dense in the blow-up. Density now descends along the partial isomorphism:
the blow-up map $\pi$ is an isomorphism over $W$ by
[thm-nagata-global-blowup-complement], hence also over the smaller
open $U\subseteq W$; since $U$ is quasi-compact and scheme-theoretically
dense in $X$, the inclusion $U\hookrightarrow W$ is scheme-theoretically
dominant, and transporting it across the isomorphism over $W$ and composing
with the dense open immersion $\pi^{-1}(W)\hookrightarrow \operatorname{Bl}_{\mathcal I}(X)$ shows that $\pi^{-1}(U)$ is
scheme-theoretically dense. For a finite composite, the inverse image of
$U$ at each stage is again a quasi-compact scheme-theoretically dense open,
so induction on the length of the composite applies the one-step lemma at
each stage.
