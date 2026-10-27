## What changed

Filled the coefficient existence/uniqueness and constructible completeness proofs in
`Sheaf.Paper.OpenCompletedRestrictionIdentification`. The finite coefficient comparison
comes from continuous cocontinuous restriction commuting with sheafification; its
constant-section equation determines it uniquely. Compatibility with coefficient
reduction produces the completed comparison, and limit projections determine it uniquely.
Restriction is additive and exact.

The original `open_completed_restriction` hole remains. Its finite-adjunction,
strict transition, tower, product and cone components were developed and checked in
isolated diagnostic files, but the full assembly exceeds the single-file compile limit.
Those diagnostic files are not part of this delivery. No new hole or intermediate
statement is introduced.

The completeness clause uses the proved intrinsic Roos completion-unit comparison and
the existing intrinsic/legacy completeness equivalence. An auxiliary prime different
from ell supplies a legacy finite-field datum; it imposes no additional condition on X.
The three theorem signatures and the coefficient data are unchanged. The item node
retains the six-step plan for its one unfinished theorem and records which clauses
are proved. To keep kernel
checking within the compile limit, the comparison records now store the same data and
normalization equations as product subtypes. Named predicates and proved accessors
preserve each equation; the change record lists the consumers and equivalence of meanings.
Proof helpers are private and proved. The representation repair is recorded in
`coord/changes/open-completed-restriction-records.md`.

## Proved and sorry left

Closed two of the three original holes:

- `WeilConjectures.OpenCompletedRestriction.coefficients_exact`.
- `WeilConjectures.OpenCompletedRestriction.open_completed_restriction_complete`.

One original hole remains:

- `WeilConjectures.OpenCompletedRestriction.open_completed_restriction`
  (`lem-pur-open-completed-restriction-identification`).

Added zero holes; split off zero statements. The completeness clause uses the existing
comparison existence theorem and proves its additional invertibility conclusion from
the intrinsic completion-unit criterion. Final packet compilation and consumer checks
are recorded by the delivery tool.

## No longer needed

Removed direct proof imports (the retained proofs use sheafification and the intrinsic
completion-unit criterion; the remaining comparison hole carries its concrete proof plan):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`
- `Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CompletedCoefficientPushforwardModels`
- `Sheaf.Paper.CompletedReductionAugmentationIso`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.Paper.IntegralReductionTowerCanonical`

Removed proof dependencies from the item node:

- `def-pc-sheaf-restrict-scalars`
- `def-pur-completed-pushforward-models`
- `lem-cbc-exact-product-functor-strict-limit`
- `lem-pc-kflat-resolution`
- `lem-pur-completed-reduction-augmentation-iso`
- `lem-pur-ring-iso-derived-transport`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-sheaf-scalar-extension-ring-iso`
- `lem-weil-strict-roos-comparison`

The obsolete top-level tool approvals for the replaced abstract route were removed, preserving the
remaining order. `def-pc-sheaf-restrict-scalars` remains a statement dependency;
its operation still appears in the unchanged statement. No global module withdrawal
is requested, and dependencies needed transitively by retained modules remain needed.


## Where the brief, the DAG or earlier work was wrong

The broad proof plan is valid. Its complete-input step can use the proved intrinsic
Roos unit comparison directly, without constructing a separate SiteLimitData record or
invoking the completed-reduction augmentation theorem. The developed finite comparison can be
constructed uniformly at independent site and coefficient universes from Mathlib's
pushforward adjunction, so no universe-specialized inverse-image theorem is required.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
