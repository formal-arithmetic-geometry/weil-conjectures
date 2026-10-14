# AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker

## Reason

Retire the standalone duplicate named by the queued upstream repair. The full
cokernel proof is preserved verbatim in local hc of pic_proper_ntorsion; the
surviving parent signature and all target statements and definitions are unchanged.
The first worker's proof-only restoration did not address the duplicate repair.

## Old

```lean
theorem Scheme.Hom.pic_proper_ntorsion_coker
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n))
```

The original parent proof calls the removed declaration:
```lean
  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
```

## New

The standalone declaration is removed; its module is an empty retirement stub.
The parent removes its import of PicProperNTorsionCoker, adds proof-only imports
PicardDecomposition and Mathlib.Algebra.Group.TypeTags.Hom, and replaces its hc
call by a typed local block with exactly the former proof. No definition changes.
The cokernel node's lean record now identifies the parent theorem's second conjunct.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | A3 | Retire duplicate declaration and its imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Forced adaptation: inline the retired cokernel proof and replace its proof imports. |

A source search found PicProperNTorsion as the sole importing/calling module.
Its original has an unknown-identifier error for pic_proper_ntorsion_coker when
compiled against the empty module; the complete delivered set compiles.
No existing target definition or surviving signature changes, so target statement
review is not reopened. The forced adaptation changes only imports and the hc proof.

## Status

landed 20261014T061022-L-2464573 2026-10-14 (merge of deliver/A3/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
