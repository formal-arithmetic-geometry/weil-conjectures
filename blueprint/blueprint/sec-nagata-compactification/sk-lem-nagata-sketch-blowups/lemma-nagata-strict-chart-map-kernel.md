+++
id = "lemma-nagata-strict-chart-map-kernel"
kind = "lemma"
title = "Kernel of the map to the extended-ideal chart"
order = 149
uses = ["def-nagata-power-torsion", "def-nagata-strict-chart-to-extended-blowup-chart", "lemma-nagata-power-torsion-kernel-localization", "lemma-nagata-strict-chart-map-surjective"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The kernel of $\sigma_a$ is exactly
$\Gamma_{(a)}(C_a(A,B,I))$.

## Proof

Both source and target map to $B_b$. The target $B[J/b]$ is the subalgebra
generated there by the fractions from $J$, and $\sigma_a$ has exactly that
image by [lemma-nagata-strict-chart-map-surjective]. Thus its kernel
is the kernel of localization at $b$. Under the $A$-action this is the
kernel of localization at $a$, which equals the $a$-power torsion by
[lemma-nagata-power-torsion-kernel-localization].
