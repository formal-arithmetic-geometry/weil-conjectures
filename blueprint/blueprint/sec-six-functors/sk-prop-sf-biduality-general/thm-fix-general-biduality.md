+++
id = "thm-fix-general-biduality"
kind = "theorem"
title = "Finite-stage Verdier biduality"
order = 2136
uses = ["lem-sf-comparison-tor-amplitude", "lem-sf-proetale-constructible-origin", "lem-weil-finite-duality-site-comparison", "lem-weil-verdier-preservation-strata", "thm-weil-etale-geometric-biduality"]
+++
Let $Y$ be a separated finite-type scheme over
$k=\overline{\mathbf F}_q$, and let $A=A_{E,n}$.
On either the small etale site or the small pro-etale site,

$$
D_Y=R\mathcal Hom_A(-,\omega_Y),\qquad \omega_Y=Ra_Y^!A,
$$

is a contravariant exact anti-equivalence of $D^b_{ctf}(Y,A)$,
and the natural map $\delta_K:K\to D_YD_YK$ is an isomorphism.
No boundary duality input is a hypothesis of this theorem.

## Proof

Etale preservation and biduality are
[lem-weil-verdier-preservation-strata], [thm-weil-etale-geometric-biduality].
Every pro-etale constructible finite-Tor complex descends to the etale
category by [lem-sf-proetale-constructible-origin], [lem-sf-comparison-tor-amplitude].
The evaluation-compatible comparison of
[lem-weil-finite-duality-site-comparison] transports both assertions
and the natural double-dual isomorphism to that category.
