## What changed

Filled all sixteen theorem proofs in `lean/Sheaf/Paper/EquivariantMatesCoefficientTransport.lean`, without changing any existing declaration signature or public definition. Added only proved private helpers for the faithful forgetful functor, heterogeneous object/map equalities, and the specified adjunction lift. The mate carrier proof retains the supplied units, counits, square and all strict carrier identifications.

The four pasting laws specialize the corresponding Mathlib mate lemmas. Coefficient transport follows directly from naturality and the supplied unit, square and counit compatibility equations. Functoriality and cancellation prove pasted transport and the composite comparison cocycle. The concrete coefficient theorems specialize this generic argument to the recorded functors. Common-stage representative equality uses the existing `representatives` theorem. The inverse is the actual carrier inverse, lifted by `Algebra.isoMk`.

Updated the node proof, proof dependencies and proof origin to match this argument. Removed two redundant private imports. No statement, definition, target, source-library file or consumer was changed. All sixteen original public theorem signatures were compared verbatim with the repository version. Edge cases remain covered by the unrestricted categorical proofs: identity functors and coefficient extensions, arbitrary Weil structures, and only conditionally invertible arrows.

Validation: remote single-file compilation through `lcompile.py`; delivery compilation and preflight through `deliver3.py`.

## Proved and sorry left

Closed 16 of 16 existing holes, with no holes added and none split off:

- `CategoryTheory.EquivariantMates.fixedPair_mate`
- `CategoryTheory.EquivariantMates.fixedPair_mate_pasting`
- `CategoryTheory.EquivariantMates.fixedPair_mate_adjunctionComposition`
- `CategoryTheory.EquivariantMates.fixedPair_mate_changeSecond`
- `CategoryTheory.EquivariantMates.fixedPair_mate_changeFirst`
- `CategoryTheory.EquivariantMates.fixedPair_inverse`
- `CategoryTheory.EquivariantMates.mate_coefficientTransport`
- `CategoryTheory.EquivariantMates.pasted_coefficientTransport`
- `CategoryTheory.EquivariantMates.compositeComparison_cocycle`
- `WeilConjectures.rational_mate_coefficientTransport`
- `WeilConjectures.rational_mate_exact`
- `WeilConjectures.finiteExtension_mate_coefficientTransport`
- `WeilConjectures.commonStage_mate_coefficientTransport`
- `WeilConjectures.commonStage_mate_representatives`
- `WeilConjectures.rational_weil_mate`
- `WeilConjectures.commonStage_weil_mate`

All belong to `lem-pod-equivariant-mates-coefficient-transport`. There is no remaining `sorry` in the delivery.

## No longer needed

Removed private imports `Sheaf.CategoryTheory.ScalarLocalization` and `Sheaf.Paper.SfRationalizationKaroubi`. The proof needs no explicit pure-tensor multiplication, linear spanning argument or scalar localization calculation: every recorded coefficient change is already a functor and the supplied comparisons encode its interaction with the operations. Accordingly `def-weil-linear-scalar-localization` and `def-weil-rationalization-karoubi` are removed as direct proof dependencies of this node. Their constructions remain present transitively in the coefficient categories and functors used in public signatures; neither node nor module is withdrawn or claimed globally unnecessary.

All other declared dependencies are used. No module is pruned globally, and no fixed blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found in the statements. The original plan's separate pure-tensor and linearity calculations were unnecessary for these Lean statements, since the coefficient functors and natural transformations already supply the required functoriality and naturality. The imported `IsoAlgebra.forget` has no directly synthesizable faithfulness instance in this compilation context, so a proved private instance supplies it by the two morphism extensionality lemmas.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
