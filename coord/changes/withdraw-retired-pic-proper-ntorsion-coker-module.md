# Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker retirement and caller adaptation

## Reason

The standalone `pic_proper_ntorsion_coker` declaration is removed; its complete proof is
inlined into `pic_proper_ntorsion`, whose signature is unchanged.

## Old

The baseline caller declaration was:

```lean
theorem Scheme.Hom.pic_proper_ntorsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃* Multiplicative (ZMod n)) ∧
    (∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L) := by
  have ht := Scheme.Hom.pic_proper_ntorsion_torsion f n _hn
  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
  have hd := Scheme.Hom.pic_proper_ntorsion_div f n _hn
  exact ⟨ht, hc, hd⟩
```

## New

The caller removes the retired-module import, adds
`Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` and
`Mathlib.Algebra.Group.TypeTags.Hom`, and replaces the `have hc` call with the complete
former cokernel proof in a typed local block. The parent theorem signature and visibility
remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Forced adaptation: remove the retired-module import and inline its cokernel proof. |

## Failure and necessity

The baseline `PicProperNTorsion` imports this module and calls
`pic_proper_ntorsion_coker`. It fails against the delivered empty module with an
unknown-constant error; the adapted caller is included in this delivery.

## Status

landed 20261014T053240-L-2010482 2026-10-14 (merge of deliver/A4/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
