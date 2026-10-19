## What changed

Proved `AlgebraicGeometry.ProEtale.isIso_finite_proetale_smooth_base_change` in
`Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange`, without changing its signature,
either existing definition, or any public import. The proof derives qcqs for h, cancels
the canonical source comparison in `comparison_derivedBaseChangeMap`, and transports
that identity along `finiteSmoothModelCoordinates` by naturality. It extracts the
etale model, converts its explicit cohomological bounds to t-structure bounds and
its finite constant-value constructibility to the source-library predicate, then uses
`Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth` to make every factor
of the conjugation invertible. Realization preserves invertibility and the identity.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
Updated the existing node's proof, proof dependencies, and origin to the actual argument.
No definitions or statements are changed, and no new declaration is introduced.
The final single-file compile passed in 8.3 seconds with no warnings.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.ProEtale.isIso_finite_proetale_smooth_base_change`
(node `sbc-thm-finite-proetale-smooth-base-change`).
Zero holes remain in the item module. Zero holes were added or split off.
This is a proof from existing declarations, not a decomposition. Transitive imported
holes, if any, remain the responsibility of their own items.

## No longer needed

Removed these five proof-only imports:

- `Sheaf.AlgebraicGeometry.BoundedDerivedSmoothBaseChange`: use the already proved
  source-library bounded-below theorem realizing the same bounded smooth-base-change
  step. The node `sbc-thm-bounded-derived-smooth-base-change` is still needed.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: the actual module-coefficient
  exchange is already supplied by the public source-library imports; its abelian and
  set-valued interfaces are not needed here. No direct proof edge to
  `sbc-def-base-change-map` remains; its statement dependency stays.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`: the source and target comparison
  isomorphisms and their exchange compatibility are already supplied by the source
  transport theorem. No separate application of
  `prop-weil-pbc-comparison-direct-image` is needed in this proof.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the source transport
  theorem already fixes the canonical pullback comparisons; the support-site coherence
  theorem `lem-weil-pbc-comparison-pullback` is not used separately.
- `Sheaf.Paper.CondensedAmbientExchange`: the statement is expressed in the fixed-scalar
  model and mapped by realization. It does not need the separate condensed internal
  module-object exchange declaration of `def-weil-pbc-ambient-ringed-exchange`.
  That node remains a statement dependency.

Removed obsolete direct tool-use approvals for the separate direct-image and pullback
comparison nodes, keeping the qcqs-permanence and exchange-transport approvals in order.
These are removals from this item's direct import/proof route, not assertions that no
other target or module uses the removed modules. The unit `sk-rem-rest` has no prescribed
proof steps; the mathematical etale-comparison route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The proof plan did not mention the conversion between
explicit finite-constant-value constructibility and the source-library constructibility
predicate; an existing proved comparison supplies it. The existing source-library
bounded-below smooth-base-change theorem is sufficient, so the separate unbounded
Sheaf theorem and its extra proof imports are unnecessary here. No arbitrary etale
model is constructed as data: the model is eliminated only inside the proof, and the
formula is proved for every given model and isomorphism.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
