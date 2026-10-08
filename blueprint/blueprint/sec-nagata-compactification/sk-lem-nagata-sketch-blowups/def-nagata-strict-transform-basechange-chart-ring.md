+++
id = "def-nagata-strict-transform-basechange-chart-ring"
kind = "definition"
title = "Affine base-change chart ring"
order = 143
uses = ["def-nagata-blowup-chart-ring"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

Let $A\to B$ be a ring map, let $I\subseteq A$, and let $a\in I$.
Define

$$
C_a(A,B,I)=B\otimes_A A[I/a].
$$

We regard $a$ as an element of $C_a(A,B,I)$ through the structural map
$A\to C_a(A,B,I)$.
