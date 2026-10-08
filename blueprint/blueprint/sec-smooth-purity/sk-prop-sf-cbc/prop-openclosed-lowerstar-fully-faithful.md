+++
id = "prop-openclosed-lowerstar-fully-faithful"
kind = "theorem"
title = "$i_*$ is fully faithful"
order = 1522
lean = ["AlgebraicGeometry.Etale.fullyFaithfulLowerStar", "AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit"]
tags = ["latex:proposition"]
uses = ["def-kun-separably-closed", "lemma-openclosed-point-ulift", "lemma-openclosed-stalk-lowerstar", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $i\colon Z\to X$ be a closed immersion. Then the counit

$$
\varepsilon\colon i^*i_*\Longrightarrow\mathrm{id}_{\shv{\et Z}}
$$

is an isomorphism; equivalently, $i_*$ is fully faithful.

## Proof

Fix $\mathcal H\in\shv{\et Z}$. By [lemma-openclosed-point-ulift] it is
enough to show that $\varepsilon_{\mathcal H}$ is an isomorphism on the stalk
at every geometric point $\bar z$ of $Z$. So fix $\bar z$ and write
$\Phi_{\bar z}$ for its stalk functor on $\shv{\et Z}$; recall that
$\Phi_{\bar z}$ is left adjoint to the skyscraper functor
$M\mapsto\mathrm{sky}_{\bar z}(M)$ of $\bar z$.

The stalk of $i^*i_*\mathcal H$ is never computed. Instead:

*Step 1.* A morphism is invertible as soon as precomposition with it is
bijective on morphisms into every object $M$ of $\mathcal A$. So it suffices
to show that

$$
(-)\circ\Phi_{\bar z}(\varepsilon_{\mathcal H})\colon
\Hom(\Phi_{\bar z}(\mathcal H),M)\to
\Hom(\Phi_{\bar z}(i^*i_*\mathcal H),M)
$$

is bijective for every $M$.

*Step 2.* The composite of $i^*\dashv i_*$ with
$\Phi_{\bar z}\dashv\mathrm{sky}_{\bar z}$ is an adjunction
$i^*\circ\Phi_{\bar z}\dashv\mathrm{sky}_{\bar z}\circ\,i_*$ (note
$\Phi_{\bar z}(i^*-)$ is the source of the map in Step 1 read at
$i_*\mathcal H$). Transposing along it turns precomposition with
$\Phi_{\bar z}(\varepsilon_{\mathcal H})$ into

$$
i_*\colon
\Hom(\mathcal H,\mathrm{sky}_{\bar z}(M))\to
\Hom(i_*\mathcal H,i_*\mathrm{sky}_{\bar z}(M));
$$

this is a formal identity of the two adjunctions, the triangle identity of
$i^*\dashv i_*$ read through the naturality of the unit of
$\Phi_{\bar z}\dashv\mathrm{sky}_{\bar z}$.

*Step 3.* Pushing forward a skyscraper along $i_*$ gives a skyscraper:
$i_*\mathrm{sky}_{\bar z}(M)$ is, on the nose, the skyscraper sheaf at the
point $i\circ\bar z$ of $\et X$ obtained from $\bar z$ by base change.
Therefore the map of Step 2 is, after transposing back along
$\Phi_{i\circ\bar z}\dashv\mathrm{sky}_{i\circ\bar z}$, precomposition with
the stalk comparison

$$
(i_*\mathcal H)_{i\circ\bar z}\xrightarrow{\ \sim\ }\mathcal H_{\bar z}
$$

of [lemma-openclosed-stalk-lowerstar], which is an isomorphism.
Precomposition with an isomorphism is bijective, so the map of Step 1 is
bijective and $(\varepsilon_{\mathcal H})_{\bar z}$ is an isomorphism.

Hence $\varepsilon_{\mathcal H}$ is an isomorphism for every $\mathcal H$,
that is, $\varepsilon$ is an isomorphism and $i_*$ is fully faithful.

The only step that is not formal is Step 3, and there the only thing to check
by hand is the compatibility of the stalk comparison with the canonical maps
from the sections over a pointed étale neighbourhood; that is where the
initiality of [lemma-openclosed-stalk-lowerstar] enters.
