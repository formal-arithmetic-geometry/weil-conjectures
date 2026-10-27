## What changed

Proved `AlgebraicGeometry.Etale.IntegrationComposition.integrationTransposeComposition`
in `Sheaf.Paper.IntegrationTransposeComposition` with its original signature and the same nine
public constructions. Added proved private categorical helpers for swapping and transporting
projection coherence, inverse-projection naturality, integration of a tensor coefficient,
composite adjunctions, and right mates. The derived-category helpers first work over a general
coefficient category, avoiding costly comparisons of concrete tensor instances. A private
congruence elaborator follows the technique in the adopted
`LowerShriekCompositionCoherence` module: it constructs equality proofs between
definitionally equal structure applications, all checked by the Lean kernel.

Replaced six unused proof imports with the already-proved adopted-source modules
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc`, and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided`. The original public imports are now in `IntegrationTransposeCompositionData`, which the item
publicly imports. The nine names and signatures are unchanged. Eight constructions move verbatim;
`unitObjectIso` now specializes an irreducible general coefficient wrapper for its former
three-factor expression, to avoid costly concrete tensor-instance comparison. Updated the item's proof plan and dependencies to describe the actual calculation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.IntegrationComposition.integrationTransposeComposition`
(node `lem-pur-integration-transpose-composition`). All four clauses have complete proof bodies. The data, unit-normalization, and iteration
modules compile; the main theorem assembly also passes its isolated check. The full packet
and delivery preflight provide final validation.
No holes added; no holes remain in any of the four delivered Lean modules. The two new
intermediate theorems `integration_unit_normalization` and `iterated_integration` are proved
in this delivery; they add zero holes. A shared data module contains the nine canonical
constructions and two general coefficient wrappers. The required delivery command compiles and audits the full packet before pushing it.

## No longer needed

Removed these proof imports and the corresponding planned dependencies:

- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`
  (`lem-pur-derived-tensor-additive-constraints`): use the canonical source-library tensor
  constraints and braided-category coherence directly.
- `Sheaf.Algebra.Homology.ExactPullbackSignedComparison`
  (`lem-pur-exact-pullback-signed-comparison`): transport through the existing natural
  isomorphism between derived and exact pullback by explicit categorical calculations.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
  (`lem-kun-derived-pullback-composition-monoidal`): only naturality and inverse cancellation
  of the actual pullback compositor are needed here.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` and
  `Sheaf.Paper.RingedProjectionTensorComposition`
  (`lem-sfb-ringed-projection-tensor-composition`): the adopted library already proves
  associativity and unitality for the actual compactification projection map. This proof
  does not reconstruct those results from the proper and open factors.
- `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`
  (`lem-pur-total-tensor-signed-coherence`): the final clause is the elementary equality
  `(-1)^((2*r)*(2*s)) = 1`; no additional shift comparison is used.

These are dependencies pruned from this item's proof, not withdrawals of their modules or
claims that other library consumers no longer need them. The existing source-library
public imports and declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of projection coherence is unnecessary: the adopted source
library contains complete proofs of `projectionMapOfCompactification_assoc`,
`projectionMap_rightUnitality`, and the braiding compatibility of derived pullback.
The invertibility assertion is also a direct consequence of
`isIso_projectionMap_of_finite`, which applies to all objects and makes its extra
specialization and orientation hypotheses redundant. They remain in the statement.

No false statement, target alteration, or forced consumer adaptation.
The unit wrapper preserves the former canonical construction; the additional projection wrapper
packages the coefficient-first projection over a general coefficient category. The definitions move to a shared module to let the two separate calculation modules import them
without an import cycle. The change record lists all three downstream consumers.

## New nodes

- `def-pur-integration-transpose-data`: the nine existing constructions, moved into
  `Sheaf.Paper.IntegrationTransposeCompositionData` and re-exported by the item.
- `lem-pur-integration-unit-normalization`: canonical projection at the tensor unit, proved
  using the adopted projection unit theorem and braiding naturality.
- `lem-pur-iterated-integration`: the ordered integration identity before any exceptional
  adjunction is used, proved using projection tensor coherence and the compositor equation.

Change record: `coord/changes/integration-transpose-data.md`.
Small-case checks: unit normalization for the identity morphism is the left-unit identity;
iterated integration for identity maps is ordinary ordered contraction by two traces. Both
calculations use only functoriality and coherent tensor isomorphisms, so zero coefficients,
empty schemes, zero traces and arbitrary unbounded inputs introduce no excluded case.
The current blueprint search for integration found its vector-bundle ancestor but no separate
statement of either calculation; searches for projection tensor and unit normalization found
no exact blueprint statement.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
