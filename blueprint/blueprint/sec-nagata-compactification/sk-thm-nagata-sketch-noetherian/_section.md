+++
id = "sk-thm-nagata-sketch-noetherian"
kind = "section"
title = "Nagata over a Noetherian base"
order = 321
uses = ["sk-lem-nagata-sketch-affine-cover", "sk-thm-nagata-sketch-two-open"]
lean = ["AlgebraicGeometry.nagataCompactification_of_isNoetherian"]
+++
*Theorem (sketch).*

Every separated finite-type morphism $X\to S$ with $S$ Noetherian
admits a compactification.

## Proof

Compactify the affine opens from [sk-lem-nagata-sketch-affine-cover].
Induct on $X_r=U_1\cup\cdots\cup U_r$. The overlap
$X_{r-1}\cap U_r$ contains the dense total intersection, so
[sk-thm-nagata-sketch-two-open] compactifies $X_r$ at each step.
The last union is $X$; the empty scheme causes no exception.

Uses: [sk-lem-nagata-sketch-affine-cover], [sk-thm-nagata-sketch-two-open]
