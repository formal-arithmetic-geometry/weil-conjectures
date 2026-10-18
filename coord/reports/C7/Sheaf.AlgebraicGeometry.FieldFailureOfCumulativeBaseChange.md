## What changed

Proved `AlgebraicGeometry.Etale.exists_fieldFailure_of_cumulativeUniversalBaseChangeProperty`
without changing its signature. The proof converts the cumulative natural degrees to every
integer below q, using the existing negative-degree vanishing theorem, then applies
`AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty` and
`AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`.

The already-existing Detection module implements the same unit's affine localization,
stalk survival and minimal-counterexample argument. Its general coefficient-ring statement
specializes directly to ULift(ZMod n); a second implementation of those steps is unnecessary.
New proof imports are Detection and Coefficients. The node proof, proof_deps, proof_origin and
obsolete tool_uses are updated to describe this reuse. Existing docstrings remain unchanged.

Verification: lcompile.py compiled the item (6.4 s) and the unchanged consumers
UniversalBaseChangeFailureDatum (8.0 s) and RelativeDimensionOneInduction (6.5 s) in import
order against the sandbox output, all with exit 0. The consumer copies were then removed
from the delivery sandbox. The public import removal and consumer checks are recorded in
`coord/changes/C7-field-failure-unused-unbounded-import.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_fieldFailure_of_cumulativeUniversalBaseChangeProperty`
(node `sbc-lem-bc-failure-field`). Added 0 holes, split off 0 statements. No sorry remains
in the item and no other Lean module is changed. This is a proof from existing library
statements, not a decomposition. Existing holes reachable through those statements remain
with their existing nodes; this delivery makes no claim to have closed them.

The degree conversion includes q=1 (only natural degree 0 is needed), negative r, and
nonnegative r. No nontriviality of ZMod n or nonemptiness of X or S is used, so n=1 and
empty schemes require no additional assumptions.

## No longer needed

Removed direct imports (22):

- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition`
- `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening`
- `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening`
- `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp`
- `Sheaf.AlgebraicGeometry.HigherDirectImageTransitions`
- `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent`
- `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection`
- `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage`
- `Sheaf.AlgebraicGeometry.BaseChangeClosedOpenEmbedding`
- `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero`
- `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.EtaleLocalityBaseChange`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`

The proof no longer directly uses the following old proof-dependency nodes; their detailed
survival argument is delegated to the existing same-unit field-detection theorem, and its
separated-base conclusion already provides the affine-morphism assertion:

- `sbc-lem-etale-locality`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `sbc-lem-bc-injectivity`
- `prop-weil-pbc-geometric-stalks-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `def-sbc-canonical-base-change-stalk-transitions`
- `lem-sbc-source-transition-thickening`
- `lem-sbc-target-transition-thickening`
- `sbc-def-base-change-map`
- `lem-sbc-stalk-transport-composition`
- `def-sbc-module-higher-image-transitions`
- `lem-sbc-source-image-limit-descent`
- `lem-sbc-target-limit-zero-detection`
- `lem-sbc-target-stalk-restriction-image`
- `lem-sbc-closed-open-coefficient-embedding`
- `lem-sbc-open-injective-coefficient-zero`
- `lem-sbc-closed-coefficient-range`
- `sbc-lem-bc-minimal-counterexample`
- `def-weil-proper-morphism`
- `def-pc-fibre-product`
- `def-weil-closed-immersion`
- `pqf-def-affine-morphism`
- `lem-pc-closed-subscheme-base-change-ideal-image`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-exchange-forget-coefficients`

These are direct dependency/import removals, not claims that all listed modules disappear
from the targets' transitive closure: Detection itself retains its own required survival
modules, and other target branches can still use these declarations. The statement dependency
`sbc-def-base-change-map` is unchanged. Of the old tool_uses approvals only
`sbc-def-base-change-property` remains; all the other old approvals are withdrawn because
this module no longer directly uses them. No Lean module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expanded an argument already implemented by the source library's
Detection module. The only interface difference is that this item supplies nonnegative
natural degrees, whereas Detection asks for all lower integer degrees. Coefficients already
proves universal base change in negative degrees, so this difference is resolved by a short
case split and natural/integer arithmetic. The current blueprint's general-ring field-detection
statement is already attached to `sk-lem-failure-field`; its universal-failure variant is in
the same module. The same unit and its route are preserved. No mathematical statement or
definition repair was required.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
