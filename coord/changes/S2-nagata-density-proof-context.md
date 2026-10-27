# AlgebraicGeometry.ProEtale.CondensedRing.nagata_density_normalization

## Reason

Remove the two inherited settings that disable respect for transparency while
proving the theorem. The proof now uses the existing generic open-restriction
normalization declaration and a private categorical adjunction lemma. No
signature, public import, definition, instance, or global attribute changes.
The conservative command checker records the removal as an interface change.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
```

The theorem's signature is verbatim unchanged. Its former `by sorry` body is
replaced by a complete proof. New imports are private proof imports only.

## Users

`tools/downstream.py Sheaf.Compactification.NagataDensityNormalization --uses
nagata_density_normalization` reports one downstream module, whose import stays
valid with the identical public interface. The only textual declaration-name
hit is in the item itself. No downstream file is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Compactification.NagataDensityNormalization | S2 | Proof and local settings only. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | X2 | Identical imported interface. |

## Status

landed 20261025T203031-L-2776935 2026-10-25 (merge of deliver/S2/Sheaf.Compactification.NagataDensityNormalization)
