# AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker

## Reason

Upstream review #1428 and coord/repairs.txt request removal of this duplicate.
The cited upstream Curve/Jacobian module and nonempty_addEquiv_torsionBy_pic_and_quotient
are absent from this checkout and its source-library checkout. Retire the standalone
public declaration and inline its existing proof in its only caller. This removes the
duplicate without relying on unavailable imports, changing any retained signature,
or bypassing any blueprint step. The module remains as a declaration-free compatibility import, retaining its public imports.

## Old

```lean
theorem Scheme.Hom.pic_proper_ntorsion_coker
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n))
```

## New

The standalone declaration is removed; its module retains only its public imports. The same calculation is the
local `hc` proof inside `Scheme.Hom.pic_proper_ntorsion`; that theorem's statement and
visibility are identical. No new public declaration, definition, axiom or sorry is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | A3 | Removed duplicate declaration; retained compatibility imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Sole direct importer and sole declaration user; replace removed import and inline the existing calculation at hc. |

`tools/downstream.py --uses` found no other declaration users among 114 transitive
importers. Since all retained signatures and public imports are unchanged, none of those
indirect users needs adaptation. No target's mathematical meaning changes.

The original consumer compiled against a sandbox copy with the retired declaration absent
fails at line 70 with:

```text
error(lean.unknownIdentifier): Unknown constant
  AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker
```

The adapted consumer compiles cleanly in 2.5 seconds. Changed lines are precisely the
private proof imports and the former call to the withdrawn declaration.

## Status

landed 20261014T044553-L-1451055 2026-10-14 (merge of deliver/A3/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
