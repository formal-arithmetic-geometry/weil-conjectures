+++
id = "lem-weil-finite-duality-site-comparison"
kind = "lemma"
title = "Finite-stage duality under the site comparison"
order = 2084
uses = ["def-weil-open-closed-recollement", "def-weil-site-perfect-complex", "lem-exc-closed-support-triangle", "lem-sf-comparison-tor-amplitude", "lem-sf-hom-comparison-finite-free", "lem-sf-hom-triangulated", "lem-sf-proetale-constructible-origin", "lem-weil-stratum-ambient-hom", "lem-weil-verdier-preservation-strata", "prop-weil-pbc-comparison-direct-image", "thm-pur-finite-coefficient-smooth-purity"]
+++
Let $X$ be a separated finite-type scheme over
$k=\overline{\mathbf F}_q$, and let
$\nu_X:X_{\mathrm{proet}}\to X_{\Et}$ be the comparison morphism.
For finite coefficients $A$, $K\in D^b_{ctf}(X_{\Et},A)$, and
$M\in D^b_c(X_{\Et},A)$, the canonical map

$$
\nu_X^*R\mathcal Hom_A(K,M)
\longrightarrow R\mathcal Hom_A(\nu_X^*K,\nu_X^*M)
$$

is an isomorphism. Moreover
$\nu_X^*\omega_{X,\Et}\cong\omega_{X,\mathrm{proet}}$, and these
comparisons identify evaluations and double-dual maps. In particular
finite-stage Verdier duality on the pro-etale constructible category
is transported from etale Verdier duality.

## Proof

The comparison for $Rj_*$, including a quasi-compact open immersion
$j$, is [prop-weil-pbc-comparison-direct-image]. The exact
comparison pullback commutes with the open restrictions and closed
direct images, as their stalk and extension-by-zero descriptions show.
Apply it to the closed-support triangle of
[lem-exc-closed-support-triangle]; the first comparison identifies
the third term with the pro-etale $Rj_*j^*$ term. Full faithfulness
of closed direct image then gives
$\nu_Z^*Ri_{\Et}^!M\cong Ri_{\mathrm{proet}}^!\nu_X^*M$.
This establishes the required closed exceptional comparison directly
from recollement, without an assertion that closed ordinary restriction
commutes with internal Hom.

The finite stratification in
[lem-weil-verdier-preservation-strata], and the triangles of
[def-weil-open-closed-recollement], reduce internal-Hom comparison
to $K=Rs_!P$, with $P$ site-perfect: internal Hom is triangulated in
the first variable by [lem-sf-hom-triangulated] (the same Hom-complex
argument applies on the pro-etale site), and the exact $\nu^*$ carries
triangles to triangles, so the comparison maps form morphisms of
triangles. On both sites the identity
of [lem-weil-stratum-ambient-hom] reads

$$
R\mathcal Hom(Rs_!P,M)
=Rs_*R\mathcal Hom(P,Rs^!M).
$$

The locally closed $Rs^!$ commutes with $\nu^*$ by the open and
closed comparisons above. The site-perfect complex $P$ of
[def-weil-site-perfect-complex] is locally a bounded complex of finite
free modules, and for such a first variable and a bounded constructible
second variable the internal Hom commutes with $\nu^*$ by
[lem-sf-hom-comparison-finite-free]; the question being local, this
applies to $R\mathcal Hom(P,Rs^!M)$. Finally $Rs_*$ commutes with comparison by
[prop-weil-pbc-comparison-direct-image]. Hence the specified
internal-Hom map is an isomorphism on every stratum generator and then
on $K$.

Locally embed $X$ as a closed subscheme of a smooth affine space.
On both sites its dualizing object is the closed exceptional inverse
image of the smooth dualizing object. Smooth purity
[thm-pur-finite-coefficient-smooth-purity] and the closed comparison
just proved identify these objects; uniqueness of the adjunction
comparisons makes the local identifications agree on overlaps.
The Hom comparisons are defined by evaluation, so they identify its
transpose, the double-dual map, as well. Finally the equivalence of
bounded constructible categories is
[lem-sf-proetale-constructible-origin], and finite Tor intervals
are preserved and detected by [lem-sf-comparison-tor-amplitude].
