## What changed

Proved `SheafOfModules.ConjugateTensorLocalization.conjugate_tensor_localization_counit`
in `Sheaf.Algebra.Homology.ConjugateTensorLocalizationCounit`, preserving every existing
statement and definition. Added proved private helpers for equivalence extension, native
K-flat tensorator invertibility, lifting the counit ratio, and representative normalization.
Added the private proof import `Sheaf.Algebra.Homology.CochainTensorModelRigidity`.
Updated the node proof to match this route. The full module compiles cleanly through
`lcompile.py` in 46.7 seconds, with zero warnings and zero local `sorry` tokens.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.ConjugateTensorLocalization.conjugate_tensor_localization_counit`
(node `lem-pd-conjugate-tensor-localization-counit`). No holes added or split off.
No `sorry` remains in the item. The proof uses the existing dependency
`SheafOfModules.SiteDerivedTensorResolvingData.counit_existsUnique`; its independent
proof remains that dependency's work. All new private lemmas have complete proofs.

## No longer needed

The item no longer directly invokes `lem-pc-kflat-resolution` or imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the published unique
extension of the native site counit supplies its all-complex determination. Removed that
node from this item's direct proof dependencies and obsolete top-level tool approval.
It remains needed transitively by the existing descent and counit constructions; no module
is withdrawn. Cochain representative rigidity supplies the existing descent interface.
No unit statement or realized proof step is bypassed, and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's direct final resolution argument can be reused through the already stated
`counit_existsUnique` API. The cochain rigidity theorem supplies full faithfulness directly
on the required cochain representatives. No mathematical statement was wrong or changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
