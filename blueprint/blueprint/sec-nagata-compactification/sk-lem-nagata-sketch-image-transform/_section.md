+++
id = "sk-lem-nagata-sketch-image-transform"
kind = "section"
title = "Images under admissible blow-up"
order = 230
uses = ["sk-lem-nagata-sketch-blowups", "sk-lem-nagata-sketch-closure"]
lean = ["AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup"]
+++
*Lemma (sketch).*

Let $h:T\to X\times_SY$ be quasi-compact and quasi-separated with
first projection factoring through an open $U\subseteq X$.
Under a $U$-admissible blow-up $X'\to X$, the image of the lifted map
$T\to X'\times_SY$ is the strict transform of $\SIm(h)$.

## Proof

Both are the scheme-theoretic closure of the same part away from the
centre. On each blow-up chart this is the kernel ideal saturated by
powers of the chart generator; see 0F3Y.

Uses: [sk-lem-nagata-sketch-blowups], [sk-lem-nagata-sketch-closure]
