# SymmetricAlgebraAffineSectionComparison proof elaboration commands

## Reason

The completed proof uses tensor notation and comparisons between equivalent scalar
structures on scheme module sections. The static interface checker treats new
file commands conservatively, even though these commands only affect elaboration
of this file. This record documents the new commands; the theorem's signature,
visibility, statement dependencies and public imports are unchanged.

## Old

```lean
set_option autoImplicit false
universe u
open CategoryTheory Opposite CategoryTheory.Functor
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
```

## New

```lean
set_option autoImplicit false
universe u
open CategoryTheory Opposite CategoryTheory.Functor
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
open scoped TensorProduct
```

The two declarations `exists_sectionEquiv` (private) and
`exists_affineSectionComparison` additionally use the local command
`set_option maxHeartbeats 800000 in`, with explanations beside them.
The repair removes the two previously added file-wide transparency options: the proof
compiles under the baseline transparency settings. No option raises the 60-second
wall-clock compilation limit. No instance,
notation definition, elaboration attribute, or public declaration was added.
Opening the existing tensor notation and setting local heartbeat options does not
change the types or meanings of any imported declarations.

## Users

`tools/downstream.py --uses exists_affineSectionComparison` lists the item itself
and its one direct user, among 195 downstream modules. No user requires an
adaptation: the exported theorem has its original elaborated type and visibility.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison | V3 | Original hole closed; all new helpers private. |
| Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonStalks | unclaimed in this snapshot | Same theorem type and public imports; proof continues to apply it unchanged. |

The other downstream modules access the unchanged theorem through this importer;
the file-local notation opening and options do not affect their elaboration.
There are no forced adaptations or changes to definitions used by targets.

## Status

landed 20261014T095139-L-867373 2026-10-14 (merge of deliver/V3/Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison)
