/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare

/-! # Pinned restriction comparisons

## References

* Stacks Project, Tags 079W, 08FE and 09RE.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem restriction_transport
    {S Y : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {T T' : Over S} (g : T' ⟶ T) (M Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s T.hom)).obj M ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomOpenRestrictionMap s B T'.hom a (perfectHomMap s g f) =
      perfectHomMap (B.ι ≫ s) g (perfectHomOpenRestrictionMap s B T.hom a f) := by
  exact perfect_hom_open_transport_square s B a g M Q f
    (fun r ↦ perfectHomOpenPullbackComparison s B r.hom a) (fun _ ↦ rfl)

/-- Restricting a pullback Hom commutes with stage and apex base-change transport
(Stacks, Tags 09RE and 0D5S). -/
theorem perfect_hom_open_restriction_transport
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) :
    (∀ (j k : Set.Ici i) (hjk : j ≤ k) (M Q : schemeDerivedCategory Y)
      (f : (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
        (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj Q),
      perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE k.property))) a
          (perfectStageMap R s j.property hjk f) =
        perfectStageMap R (B.ι ≫ s) j.property hjk
          (perfectHomOpenRestrictionMap s B
            (Spec.map (R.map (homOfLE j.property))) a f)) ∧
    (∀ (j : Set.Ici i) (M Q : schemeDerivedCategory Y)
      (f : (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
        (derivedPullback (pullback.fst s
          (Spec.map (R.map (homOfLE j.property))))).obj Q),
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (perfectLimitMap R c s j.property f) =
        perfectLimitMap R c (B.ι ≫ s) j.property
          (perfectHomOpenRestrictionMap s B
            (Spec.map (R.map (homOfLE j.property))) a f)) := by
  constructor
  · intro j k hjk M Q f
    exact restriction_transport s B a
      (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
      (T' := Over.mk (Spec.map (R.map (homOfLE k.property))))
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) M Q f
  · intro j M Q f
    exact restriction_transport s B a
      (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.property)])) M Q f

end
end AlgebraicGeometry
