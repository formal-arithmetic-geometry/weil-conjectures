+++
id = "cor-coef-verdier-weil-equivariance"
kind = "theorem"
title = "Weil equivariance of the completed coefficient duality"
order = 2241
tags = ["latex:corollary"]
uses = ["def-weil-weil-sheaf-complex", "lem-coef-integral-finite-extension", "lem-coef-rational-operations", "lem-fix-weil-operations", "thm-coef-qbar-verdier", "thm-coef-rational-verdier"]
+++
For a scheme over $\mathbf F_q$, duality at $E$ and
$\Qlb$ preserves the category of Weil complexes on its
geometric fiber. Evaluation, biduality, the exceptional adjunction
data, and the finite scalar-extension comparisons are Weil
equivariant. This assertion does not require a
Frobenius-stable integral lattice for a rational Weil complex.

## Proof

The underlying operations now preserve the relevant constructible
categories by [thm-coef-rational-verdier], [lem-coef-rational-operations], [thm-coef-qbar-verdier].
Consequently the equivariance construction of
[lem-fix-weil-operations] applies, including to the
dualizing object supplied by the exceptional adjoint. Write
$g$ for geometric Frobenius and
$\theta_K:g^*K\xrightarrow{\sim}K$ for a Weil structure in
[def-weil-weil-sheaf-complex]. The dual Weil structure is
the composite

$$
g^*DK\xrightarrow{\sim}D(g^*K)
\xrightarrow{D(\theta_K^{-1})}DK.
$$

The first map is the internal-Hom comparison for the equivalence
$g^*$, using the dualizing Weil structure. Naturality of
evaluation proves its equivariance, and transposition gives the
same conclusion for $\delta$. This works with a rational
$\theta_K$ itself; it is unnecessary to reduce that
automorphism on a chosen integral lattice. At $\Qlb$ the
finite diagram representing $K$, $\theta_K$, and its
inverse is realized at one common finite coefficient field.

The comparisons in [lem-coef-integral-finite-extension]
are built from scalar tensor, the dualizing counit, and evaluation.
Their finite-level comparisons commute with the Frobenius
automorphism square, and normalized tower transport preserves
that equality. Their rationalizations and common-stage images
therefore commute with the displayed dual Weil structure. The
same units and counits as in [lem-fix-weil-operations]
give the exceptional-adjunction assertion.
