+++
id = "sk-l-dl-general-quasifinite"
kind = "section"
title = "Quasi-finite morphisms"
order = 2817
lean = ["AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite", "AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite", "AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite"]
uses = ["sk-d-dl-general-weights", "sk-prop-sf-cbc"]
+++
*Lemma (sketch).*

If $f_0$ is separated and quasi-finite, then $R^if_{0!}=0$ for $i>0$,
and $f_{0!}$ preserves mixedness and upper weight bounds.

## Proof

Compact-support base change identifies the stalks with cohomology of a
finite geometric fiber, concentrated in degree zero. Thus $f_{0!}$ is
exact. At a closed point $y$, Frobenius permutes the stalk summands.
For an orbit of length $e$, an eigenvalue $\alpha$ upstairs gives
eigenvalues $\beta$ downstairs with $\beta^e=\alpha$; since
$q_x=q_y^e$, their normalized weights agree. Pure sheaves therefore
stay pure, and exactness transports a mixed filtration.

Uses: [sk-d-dl-general-weights], [sk-prop-sf-cbc]
