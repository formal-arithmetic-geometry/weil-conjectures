+++
id = "lemma-nagata-strict-chart-to-extended-blowup-chart"
kind = "lemma"
title = "Well-definedness of the extended-ideal chart map"
order = 147
uses = ["def-nagata-strict-chart-to-extended-blowup-chart"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The assignment defining $\sigma_a$ respects addition, multiplication, the
localization relations in $A[I/a]$, and the two $A$-algebra structures.
Consequently $\sigma_a$ is a well-defined $B$-algebra homomorphism.

## Proof

For $x,x'\in I$, the relations

$$
\frac{x+x'}a=\frac xa+\frac{x'}a,
\qquad
\frac xa\frac{x'}a=\frac{xx'}{a^2}
$$

have the same images in $B_b$. The image of $A$ through the left tensor
factor equals its image through the chart factor. The universal properties
of $A[I/a]$ and of $B\otimes_AA[I/a]$ therefore give the stated map, and
its displayed formula determines it uniquely.
