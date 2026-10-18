# finiteField_absoluteGaloisGroup

## Reason

The completed proof does not use the separable-closure finite-subextension membership
lemma. Remove its unused public import. Add proof-only imports for the proved Frobenius
fixed-element theorem and infinite Galois correspondence. The theorem signature and all
existing definitions are unchanged. New helper theorems are private and fully proved.

## Old

```lean
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
```

The section had `open scoped Polynomial`, with no `open CategoryTheory` and no local
`set_option autoImplicit false` command.

## New

The unused import above is removed. The new proof-only imports are:

```lean
import Mathlib.FieldTheory.Galois.Infinite
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
```

The existing `open scoped Polynomial` is retained, `open CategoryTheory` resolves morphism
notation in the private completion helper, and `set_option autoImplicit false` enforces
explicit binders. None changes an existing declaration signature or a target's meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.FieldTheory.FiniteFieldAbsoluteGalois | S7 | The sole theorem is proved, unchanged signature. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Sole downstream module; no adaptation required. Its signatures and definitions use no declarations supplied only by the removed import. Its existing public import closure independently reaches WeilConjectures.Mathlib.FieldTheory.IsSepClosed. |

`python3 tools/downstream.py Sheaf.FieldTheory.FiniteFieldAbsoluteGalois --uses
finiteField_absoluteGaloisGroup` lists the sole downstream module above and no external
textual uses of the theorem (its consumer proof is still sorry). The consumer's public
import closure was checked from project sources. Its existing signatures remain identical;
no public definition or target statement is changed, so no target definition review reopens.

## Status

landed 20261018T145114-L-3644473 2026-10-18 (merge of deliver/S7/Sheaf.FieldTheory.FiniteFieldAbsoluteGalois)
