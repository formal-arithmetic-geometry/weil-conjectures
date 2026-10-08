+++
id = "sk-thm-transport"
kind = "section"
title = "Transport through the coefficient stages"
order = 2448
uses = ["sk-cor-trace", "sk-def-ops", "sk-def-set", "sk-thm-derived-duality", "sk-thm-frobenius", "sk-thm-sf-identification", "sk-thm-sf-package"]
+++
*Theorem (sketch).*

In the setting of [sk-def-pairing], the derived isomorphism of
[sk-thm-sf-identification], its degreewise form under the hypotheses of
[sk-thm-sf-identification] and [sk-thm-derived-duality], the trace isomorphism
and the Frobenius statements are
compatible with finite reduction, and they are realized over $\Oe$, over
$E$ and over $\Qlb$ by the uniform-tower reconstruction and by descent
along the common-stage construction. (Blueprint 15,
thm:pod-finite-reduction,
thm:pod-adic-reconstruction-and-scalar-extension,
thm:pod-qbar-coefficient-pairing.)

## Proof

*Step 1 (finite reduction).* The pairings at the levels $A_{E,n}$
are the reductions of one another: $\beta_K$ is built from the cup
product, the evaluation and the trace, and each of these is compatible with
finite reduction by [sk-thm-sf-package] (3) and [sk-def-ops]. The inverse adjoints
therefore form a morphism of normalized systems, and the isomorphism of
[sk-thm-sf-identification] descends level by level
(thm:pod-finite-reduction).
*Step 2 (the integral and field stages).* The uniform-tower
reconstruction realizes the system over $\Oe$ with one common amplitude;
localization $\Oe\to E$, extension of the coefficient field and the passage
to the common stage $\Qlb$ then transport the isomorphism, its degreewise
form and the trace isomorphism by flat extension of scalars, while the
Frobenius statements transport as well because the Weil data are defined
stagewise and the comparison maps are equivariant
(thm:pod-adic-reconstruction-and-scalar-extension,
thm:pod-qbar-coefficient-pairing).
*Step 3 (what is transported).* The transported data are exactly the
isomorphism, its degreewise form, the map of [sk-cor-trace] and the
equivariance and similitude of [sk-thm-frobenius] (a) at every stage,
together with its reciprocity clause (b) at the field stages $E$ and
$\Qlb$ only, where the degreewise form is perfect; each
of these is constructed from the pairing and the trace alone and no further
input enters.

Uses: [sk-cor-trace], [sk-def-ops], [sk-def-set], [sk-thm-derived-duality], [sk-thm-frobenius], [sk-thm-sf-identification], [sk-thm-sf-package]
