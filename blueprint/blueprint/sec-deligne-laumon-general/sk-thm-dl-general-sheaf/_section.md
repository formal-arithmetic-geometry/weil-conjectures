+++
id = "sk-thm-dl-general-sheaf"
kind = "section"
title = "Deligne–Laumon direct-image bound"
order = 2845
lean = ["AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField"]
uses = ["sk-d-dl-general-weights", "sk-i-topology", "sk-l-dl-general-composition", "sk-l-dl-general-excision", "sk-l-dl-general-normalization", "sk-l-dl-general-quasifinite", "sk-p-dl-general-relative-line"]
+++
*Theorem (sketch).*

For a separated finite-type morphism $f_0:X_0\to Y_0$ and a
constructible Weil sheaf $F_0$ mixed of weights at most $w$,
$R^rf_{0!}F_0$ is mixed of weights at most $w+r$ for every $r$.

## Proof

First prove the assertion for every affine-line projection
$\pi_0:\mathbf A^1_{Y_0}\to Y_0$, by Noetherian induction on the base.
On a dense open of each integral component, stratify the source and
use a mixed filtration to reduce to pure sheaves lisse on their strata.
A stratum dominating $Y_0$ is either an open in the relative line or
has generic relative dimension zero. After shrinking $Y_0$, the first
case is [sk-p-dl-general-relative-line] and the second is
[sk-l-dl-general-quasifinite]. Nondominating strata disappear on this
open; the discarded part of the base is covered by induction.
Open–closed reduction restores the strata and filtrations.

For general $f_0$, use Noetherian induction and finite affine
stratifications of source and target. Reduce to a dominant affine map
of integral schemes, replacing the target by the closure of the image
when necessary. By [sk-l-dl-general-normalization], its restriction
over a dense open factors through a finite map and successive
affine-line projections. The quasi-finite and composition lemmas apply
to this factorization. The complements have smaller support and are
restored by [sk-l-dl-general-excision]. This proves the sheaf assertion.

Uses: [sk-d-dl-general-weights], [sk-l-dl-general-composition], [sk-l-dl-general-excision], [sk-l-dl-general-normalization], [sk-l-dl-general-quasifinite], [sk-p-dl-general-relative-line]
