+++
id = "lemma-nagata-strict-transform-chart-localization-data"
kind = "lemma"
title = "Localization data for strict-transform chart quotients"
order = 154
uses = ["def-nagata-strict-transform-chart-ring", "lemma-nagata-power-torsion-localization"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

For $s\in B$, the canonical map

$$
(C_a(A,B,I)/\Gamma_{(a)}C_a(A,B,I))_s
\longrightarrow
C_a(A,B_s,I)/\Gamma_{(a/1)}C_a(A,B_s,I)
$$

is an isomorphism. These isomorphisms are compatible with further
localization: the maps obtained by localizing successively at $s$ and $t$
agree with localization at $st$.

## Proof

Localization commutes with tensor products, so
$(B\otimes_A A[I/a])_s\cong B_s\otimes_A A[I/a]$. By
[lemma-nagata-power-torsion-localization], the image of the
$a$-power-torsion submodule is exactly the $a/1$-power-torsion submodule.
The universal property of quotients gives the displayed isomorphism.
Compatibility for $s,t$ follows because both composites send pure tensors
and chart fractions to the same elements of the $st$-localization.
