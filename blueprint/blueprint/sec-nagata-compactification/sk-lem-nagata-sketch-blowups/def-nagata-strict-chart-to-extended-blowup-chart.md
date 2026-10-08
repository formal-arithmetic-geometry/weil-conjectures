+++
id = "def-nagata-strict-chart-to-extended-blowup-chart"
kind = "definition"
title = "Map to the blow-up chart of the extended ideal"
order = 146
uses = ["def-nagata-blowup-chart-ring", "def-nagata-strict-transform-basechange-chart-ring"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

Let $J=IB\subseteq B$, let $b$ be the image of $a$ in $B$, and write
$B[J/b]$ for the corresponding chart ring. Define

$$
\sigma_a\colon C_a(A,B,I)\longrightarrow B[J/b]
$$

on pure tensors and chart generators by

$$
\sigma_a\bigl(y\otimes(x/a)\bigr)=y\,\overline x/b.
$$
