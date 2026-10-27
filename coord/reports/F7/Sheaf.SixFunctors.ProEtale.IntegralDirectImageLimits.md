## What changed

Replaced the single proof hole in
`AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits` by a complete
categorical assembly from three smaller statements. The existing signature and
all four public imports are unchanged. New private helpers prove inverse-mate
uniqueness from the unit equation, reflection of derived isomorphisms by exact
faithful scalar restriction, the finite projection by the triangle five lemma,
and transport of the signed Roos triangle through a product-preserving
triangulated functor. The two Roos helper proofs reuse the argument already proved
in `IntegralCompletionPresentation`, without importing its unrelated presentation API.

Added three new theorem modules, each with its node and full source-based proof
in words. The tower theorem takes the finite projection isomorphisms as explicit
hypotheses, so it leaves only compatibility of levels, transitions and units.
The original theorem proves these hypotheses using the cone comparison. The new
abbreviation and definition construct the exact scalar and geometric mates.
There is no arbitrary witness chosen in a definition and no changed target.

Change record: `coord/changes/F7-integral-direct-image-reduction.md`.

## Proved and sorry left

Closed the body hole of
`AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits` (one of one
original holes); zero `sorry` remain in the item module. This is a decomposition,
not a completed axiom-free proof: three new holes remain, each the entire proof
of a public named theorem in its own module:

- `AlgebraicGeometry.ProEtale.integral_reduction_pullback_normalization`, node
  `lem-sfb-integral-reduction-pullback-normalization`.
- `AlgebraicGeometry.ProEtale.integral_direct_image_reduction_cone`, node
  `lem-sfb-integral-direct-image-reduction-cone`.
- `AlgebraicGeometry.ProEtale.integral_direct_image_reduction_tower`, node
  `lem-sfb-integral-direct-image-reduction-tower`.

The cone statement covers only the finite projection part and stops before the
five lemma; it asserts neither scalar mate invertibility nor completeness. The
normalization statement concerns inverse image alone and contains no direct
image or completeness conclusion. The tower statement assumes the separately
proved finite projection isomorphisms and contains no derived limit or
completeness conclusion. The Lean assembly supplies the remaining mate
identification, reflection, five lemma, product and signed Roos arguments.
Existing `AdicCompletion.isDerivedComplete_of_roos` is used as stated; its own
remaining dependencies are not duplicated here.

Edge checks: finite index zero means exponent one and never exponent zero; the
argument imposes no openness, properness, finite-type, boundedness or
constructibility hypothesis. The unit and tensor formulas work for zero complexes
and empty schemes. Scalar restriction is faithful and exact even for a nonflat
quotient, and invertibility of a mate is proved rather than inferred from
invertibility of the original square. The triangle comparison retains the
connecting-arrow sign. No finite-limit-preservation instance is asserted for
extension along the nonflat residue quotient.

## No longer needed

Removed these proof imports from the item module:

- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.DerivedNakayamaResolution`.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`.

Their declarations are inputs to the smaller normalization/cone/tower arguments,
not direct inputs to the categorical assembly. Consequently this delivery does
not claim these modules are globally pruned. The old direct proof dependencies
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-standard-quotients-perfect`, `det-pe-derived-nakayama-resolution`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`lem-pd-module-ringed-topos-derived-comparison`, and
`prop-weil-pbc-direct-image-limits` have been replaced in the item's proof plan
by the three concrete comparison steps; their mathematical inputs remain below
those steps as needed. No module or node is withdrawn. No adopted source
library declaration, attribute or public import is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan describes transport through the section-action equivalence, but
the stated general direct-image theorem uses a different coefficient presentation.
It does not directly identify the actual internal inverse mate or the canonical
completion-unit maps in this item's signature. The new obligations isolate those
identifications. The existing `internal_scalar_pullback_normalization` gives a balanced comparison
with a computation-counit normalization; the new normalization obligation additionally
pins its exact scalar-unit equation for the stated `derivedComapUpperStarIso` and
exact geometric pullback. Its node explicitly cites that general construction.
The existing `derivedPullIso` cannot be applied to the residue
quotient: it requires flat extension of coefficients. The proof therefore uses
an explicitly unit-normalized K-flat comparison, not that flat-only API.

The blueprint ancestor helper cannot follow `created.item` for the historical
item because it names a module instead of a DAG node. The new nodes retain the
explicit ancestor `det-thm-sf-pf-adic-open` already recorded by the item and cite
its current Completeness and Reduction paragraphs. The unit's route is retained.
No mathematical statement is disputed.

## New nodes

`lem-sfb-integral-reduction-pullback-normalization`: the finite pullback/scalar
comparison with its actual adjunction-unit equation, in
`IntegralReductionPullbackNormalization.lean`. The equation makes its induced mate
unique, so the assembly proves invertibility of the specified map.

`lem-sfb-integral-direct-image-reduction-cone`: two distinguished scalar triangles
and their comparison with identity first two components, in
`IntegralDirectImageReductionCone.lean`. The assembly supplies the five lemma and
reflects the resulting scalar-restricted isomorphism.

`lem-sfb-integral-direct-image-reduction-tower`: finite quotient comparison
isomorphisms retaining all transitions and units, under the independently proved
finite projection hypotheses, in `IntegralDirectImageReductionTower.lean`. The
assembly transports the signed Roos triangle and invokes the existing completeness
criterion. These three steps are smaller parts of the original proof, not aliases
for the original combined statement.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
