## What changed

Proved the two remaining theorems in
`Sheaf.Paper.ConstantCoefficientScalarNormalization` without changing any existing
statement, definition, universe, or public import.

The regular-module change-of-rings isomorphism is multiplication on pure tensors.
Its inverse sends one to one tensor one. The ordinary scalar chain comparison,
precomposed with this inverse in degree zero, has the required quotient coordinates
and zero shifted cone component. Maps from the regular single complex are determined
on one; the product and cone projections prove uniqueness.

For invertibility, specialize `finiteFreeCompletedScalarComparison` to the complete
regular coefficient object. Its normalized descent equation, the K-flat counit's
invertibility, and cancellation show that the localized chain comparison is an
isomorphism. Uniqueness identifies its regular-module composite with the specified
scalar unit. The auxiliary finite-field datum is constructed from an explicitly
chosen prime greater than l and the algebraic closure of its prime field.

All added helpers are private and proved. One `run_tac` assigns the already-available
K-flat counit proof directly to its definitionally equal goal: elaborator unification
otherwise expands the sheafified tensor repeatedly. Normal kernel checking verifies
that conversion; no kernel check is disabled.

Updated Step 9 and the dependency union of
`lem-weil-constant-coefficient-objects-constructible` to record this route through
`lem-weil-finite-free-completed-scalar-comparison` and
`lem-pur-derived-change-of-rings`. The other proof steps are retained.
Added proof imports for the tensor equivalence, infinitude of primes, and tactic API.

The complete module compiled cleanly through `lcompile.py` in 31.9 seconds, then
again with the redundant imports removed in 32.2 seconds. No scratch modules or
coefficient-definition experiments are included in this delivery.

## Proved and sorry left

Closed both existing holes (2 of 2):

- `WeilConjectures.constantCoefficientScalarUnit_existsUnique`.
- `WeilConjectures.constantCoefficientScalarUnit_isIso`.

Zero holes remain in the item. Zero holes were added and zero statements were split
off. The existing proof of
`WeilConjectures.constantCoefficientRationalScalarIso_existsUnique` is retained and
is not counted as new progress. Dependencies that remain unproved elsewhere are the
existing named declarations of the recorded DAG, as intended by stage 3.

## No longer needed

Removed these 15 redundant proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`.
- `Sheaf.Paper.SfCommonStageWeilCohomology`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.

The scalar normalization proof uses the already-stated regular coefficient
constructibility/completeness result and the finite-free comparison instead of
repeating the stalk, constructibility and surjective-tower arguments here. The shared
node still records those arguments in Parts 1 and 2, whose declarations are re-exported
by `ConstantWeilStructure`; their nodes therefore remain needed. The unit-route imports `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` are retained as required by
the unit-route preflight. No node or module is
claimed to leave the targets' transitive import closure. All three existing public
imports are retained.

## Where the brief, the DAG or earlier work was wrong

The first dry run required retaining those two unit-route imports and a change
record for the private proof setup commands. Both are included in the revised
packet. The record is
`coord/changes/D4-constant-scalar-normalization-proof-context.md`.

No false statement or signature defect was found. The original Step 9 plans a direct
surjective-tower calculation; the recorded finite-free comparison supplies a shorter
route with the same strict normalization. The earlier scratch attempt to infer the
unit's invertibility directly did not justify it; the delivered proof uses the
normalized descent equation and the K-flat counit explicitly.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
