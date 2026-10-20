# AlgebraicGeometry.IsCoherentRelativeDualizingPair

## Reason

Restore the assigned quarantined module after the upstream derived-pullback migration.
Use the upstream declaration directly and remove the unused generic universe-Hom import.
The nine original public declarations, all their signatures and all definition bodies
are preserved. The only original proof hole is now fully proved.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The old Sheaf derived-pullback module is already a withdrawn empty module. All
actual pullback and ordinary derived-Hom declarations used here come from the
upstream public imports. No signature or definition is changed. The removed
universe-Hom module supplied no declaration used by this module's statements or bodies.
The sheaf tensor universal property and single-factor total-complex comparison are
private proof imports. No upstream file is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeDualizingPair | X2 | Restored from the rework archive; canonical upstream pullback imported; one proof completed. |
| Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison | unclaimed, quarantined | No adaptation: public signatures and data definitions used here are identical. It already imports DerivedInternalHomOfUniverses explicitly. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed, quarantined | No adaptation: public signatures and data definitions used here are identical. Its universe-Hom proof dependency comes through its explicit RhomGlobalSectionsOfUniverses import. |

No live module currently imports the quarantined item. The two archived direct
consumers were read, including their imports and all uses of the item's declarations.
Their independent quarantine repairs remain assigned separately; they are not withdrawn.
The existing DAG attachment, statement dependencies and the unit route are retained.
The change only removes an unused public import and migrates to the canonical pullback
module; target meanings do not change and no target-statement review is reopened.

## Status

landed 20261020T174922-L-821480 2026-10-20 (merge of deliver/X2/Sheaf.AlgebraicGeometry.RelativeDualizingPair)
