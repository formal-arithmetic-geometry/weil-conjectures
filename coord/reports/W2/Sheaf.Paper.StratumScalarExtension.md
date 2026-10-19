## What changed

Proved `AlgebraicGeometry.Scheme.stratumScalarExtension` without changing its signature or its three section definitions. The constant-module comparison uses the module sheafification/global-sections adjunction and is normalized on every constant section. A private, proved scalar-extension comparison uses the existing identity-on-sections direct-image comparison, composite adjunctions and their unit equation. Naturality assembles the complex isomorphisms. The generic ringed-topos theorem gives K-flatness and flat terms; exact derived pullback supplies cohomology comparison.

Added and proved `AlgebraicGeometry.Scheme.proEtaleAlgebraicInverseImage_exists` in `Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage`. The existing unit-normalized underlying-set identifications give the ring and module comparisons. Transposing through the set adjunction proves module naturality and all seven operation graph equations from the ring and module unit laws. The module functor is the existing construction itself, with reflexive equality. No definition chooses arbitrary data from unproved mere existence.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.stratumScalarExtension`.
The new theorem `AlgebraicGeometry.Scheme.proEtaleAlgebraicInverseImage_exists`, node `lem-sp-proetale-algebraic-inverse-image`, is also proved. Added holes: zero. Remaining holes in the delivered modules: zero. The proofs use existing named dependencies that may themselves still contain sorry; this delivery does not claim their axioms have been eliminated.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`, `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (already publicly available), `Sheaf.CategoryTheory.ModulePullbackTensorIso`, `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`, and `Sheaf.Paper.SfCommonStageWeilCohomology`. Public imports are retained for consumer compatibility.

The proof avoids the original set-valued constant-object detour and generic tensor-product pullback comparison. It does not use `lem-weil-pbc-constant-sheaf-maps-global-sections`, `lem-weil-pbc-sheafification-sets-exact` or `lem-weil-pbc-ringed-topoi-module-pullback-tensor`. The specialized finite coefficient nodes `prop-weil-pbc-proetale-constant-ring-map` and `prop-weil-pbc-proetale-constant-exact` are replaced by the arbitrary constant-ring operations already used by the signature. Their obsolete top-level tool_uses entries are removed. The algebraic-presentation proof uses the ring/module identification declarations of `lem-pur-proetale-inverse-image-tensor-comparison`; it does not need that node's tensor, coefficient quotient, or composition conclusions. The previous proposed bridge route through `lem-weil-pbc-proetale-model-ring-presentation`, `new-lem-weil-pbc-proetale-module-canonical-unit`, and `lem-weil-pbc-adjunction-lifts-group-ring-objects` is unnecessary as a direct proof dependency. No unit statement or realized step is bypassed (the unit has empty realized step lists).

## Where the brief, the DAG or earlier work was wrong

The generic K-flat theorem requires an `AlgebraicInverseImage` presentation, which the original recorded inverse-image declaration did not supply. The normalized underlying-set identifications in `ProEtaleInverseImageTensorComparison` do supply the missing ingredients: adjunction injectivity derives their naturality and operation equations. The previous sandbox's proposed split-off is therefore proved here. The direct-image comparison uses a different presentation from `proEtaleConstantRingPushforward`, so the proof includes the identity-on-sections bridge justified by the ring adjunction triangle identity. No statement is disputed. The algebraic bridge works for empty schemes, zero rings and modules, identity morphisms and arbitrary scheme morphisms; it makes no finite-coefficient or immersion assumption. No existing definition or statement changes. Preflight nevertheless flags the proof-support openings and section variables; `coord/changes/stratum-scalar-extension-proof-context.md` records these commands and the unchanged effect on all downstream consumers.

## New nodes

`lem-sp-proetale-algebraic-inverse-image`: the proved algebraic presentation of the specified inverse-image module functor, sourced to Stacks Tags 00YV and 03D2 and parent proof paragraph (2). Blueprint search for algebraic inverse image found no matching blueprint node. Mathlib searches are recorded in the actual search log. Its Lean proof uses the existing normalized underlying-set identification declarations, followed by adjunction injectivity, not a new unproved premise.

Change record: `coord/changes/stratum-scalar-extension-proof-context.md`.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
