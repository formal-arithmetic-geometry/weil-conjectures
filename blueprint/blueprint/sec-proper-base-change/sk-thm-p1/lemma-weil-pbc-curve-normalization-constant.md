+++
id = "lemma-weil-pbc-curve-normalization-constant"
kind = "lemma"
title = "Normalization and smooth constant case"
order = 1181
uses = ["lemma-weil-pbc-curve-dense-open-reduction", "lemma-weil-pbc-normalization-exact-sequence", "lemma-weil-pbc-smooth-curve-artin-schreier", "lemma-weil-pbc-smooth-curve-kummer-localization"]
+++
For a reduced curve, extension-invariance for $j_!\underline{\mathbf F_\ell}$
reduces through the finite normalization to the corresponding calculation on
a smooth curve, both for proper and affine opens and also when
$\ell=\operatorname{char}k$.

## Proof

The normalization $X^\nu$ is a finite disjoint union of smooth curves and
points. On a component disjoint from $U^\nu$ the extension-by-zero sheaf is
zero and every assertion is immediate; on every other component $U^\nu$ is
dense. The dense-open localization lemma on $X^\nu$ therefore reduces
$j^\nu_!\underline{\mathbf F_\ell}$ to the constant sheaf on each remaining
smooth component, with the five-term sequence and all comparison maps
already specified there. If $\ell\ne\operatorname{char}k$, apply the Kummer and
localization calculation; if $\ell=\operatorname{char}k$, apply the
Artin–Schreier calculation. Thus all applicable eight assertions hold for
$j^\nu_!\underline{\mathbf F_\ell}$.

Exact finite direct image transfers them to
$\nu_*j^\nu_!\underline{\mathbf F_\ell}$. The normalization exact sequence
then transfers them to $j_!\underline{\mathbf F_\ell}$, including the
low-degree comparison maps and assertion (8). Properness is preserved by
finite normalization; affineness is preserved because a finite morphism
over an affine is affine. This completes the normalization, proper/affine
localization, prime-to-characteristic, and characteristic-$\ell$ branches
without an unnamed smooth-curve calculation.
