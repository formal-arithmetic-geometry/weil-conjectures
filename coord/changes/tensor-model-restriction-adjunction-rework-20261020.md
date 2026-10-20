# TensorModelRestrictionAdjunction imports after upstream synchronization

## Reason

Restore the assigned quarantined module from
`quarantine/Sheaf/AlgebraicGeometry/TensorModelRestrictionAdjunction.lean`.
The rework record reports a duplicate `CategoryTheory.derivedInternalHom`
loaded from the old Sheaf dependency tree and the adopted source tree.
The old public augmentation import has since become an empty withdrawn module.
The theorem needs the derived tensor structure and the original K-flat predicate,
not the augmentation definition. Import those statement dependencies directly.

## Old

The archived import block, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
```

## New

```lean
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
```

Every declaration signature, proof body, local attribute and option is preserved
verbatim from the archive. No definition or target meaning changes. The original
Lean attachment and both proof dependencies remain valid.

## Users

`tools/downstream.py` reports the item as an unknown module because its source
is quarantined. A source search of both `lean/` and `quarantine/` finds one
importer. The source-library theorem of the same name uses a separate upstream
module and does not import this Sheaf module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction | N2 | Restore with direct statement imports; all declarations unchanged. |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | unclaimed; quarantined | Its call uses the same theorem signature. Its own augmentation import requires its separately listed upstream-sync rework. |

The unchanged, already landed source of
`Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons` is included in the
sandbox only to recompile against its repaired imports. The published artifact
initially still loaded the old internal-Hom module. It adds no source diff.

## Status

landed 20261020T154620-L-3137337 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction)
