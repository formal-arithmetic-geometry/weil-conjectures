## What changed

Proved `WeilConjectures.integralConstructible_locallyComplete` in
`Sheaf.Paper.AmbientCompletedTensorAdjunction`, without changing its signature or any
other public declaration. The completeness clause of `sfIntegralConstructible` is
transported by `sfDerivedComplete_iff_legacy`. An auxiliary prime greater than the
coefficient prime supplies an admissible finite-field datum. Essential surjectivity
of the good-representative localization supplies the representative required by
`roosIntrinsicCompletenessEquivalence`; its first implication gives exactly the
local vanishing condition. `PrincipalKoszulStrictReplacement.coefficient_datum`
supplies the principal coefficient datum. No bounds on tensor inputs enter this proof.

Added private proof imports of `SfDerivedCompleteLegacyComparison`, the prime
infinitude theorem, and access to the existing private good-localization proof in
`IntegralDerivedOperationsOnSlices`. Updated the item's DAG proof step and dependency
list to record the Sf/legacy comparison. Existing statements and definitions remain
unchanged. The instance exclusions are scoped to the proved theorem.

## Proved and sorry left

Closed one of the original four holes:
`WeilConjectures.integralConstructible_locallyComplete`.

Three original holes remain, all attached to
`lem-sf-ambient-completed-tensor-adjunction`:

- `CategoryTheory.AmbientCompletedTensor.finiteTensorStep_existsUnique`.
- `CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction`.
- `WeilConjectures.integralAmbientCompletedTensorAdjunction`.

Added zero holes and zero split statements. This is a partial delivery of the
module, not a proof of either tensor adjunction.

## No longer needed

Removed the following unused private imports from this module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.

No node or module is withdrawn. These imports are unnecessary for the implemented
proof and the current declarations, but the unresolved adjunction still has its
planned dependencies in the DAG; this delivery does not claim to prune that route.

## Where the brief, the DAG or earlier work was wrong

The constructible specialization additionally needs the existing Sf/legacy
completeness comparison; it is now an explicit proof dependency. The auxiliary
prime may be any prime distinct from the coefficient prime, so choosing one above
it avoids a case distinction. No statement defect was found.

The attempted integral reflector transport required a Hom-bijection assertion
beyond the output-completeness and invertible-unit assertions of the integral
cone criterion. A draft attempted to transport the singleton reflector through a small model
and the normalized cone comparison; its universe and unit-comparison elaboration
was not completed. That draft and the unfinished total-tensor comparison are not delivered.
The retained proof has no such comparison or new helper theorem.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
