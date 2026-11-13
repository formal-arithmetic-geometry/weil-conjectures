/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection

/-! # Evaluation comparisons with a K-injective second representative

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option maxHeartbeats 1000000 in
-- Elaborating the restriction and Hom models requires additional heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The restriction and Hom models use equivalent localized-site carriers.
/-- The local evaluation square when its second representative is already K-injective.
This only handles the resolved case; it does not assert the comparison for an arbitrary
second complex.
-/
theorem exists_strictlyPerfect_kInjective_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    [F.IsKInjective]
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
  let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
    ((α_ N D K).hom ≫ N ◁
      ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
        (ρ_ N).hom)
  obtain ⟨r, hr⟩ := exists_strictlyPerfect_evaluation_local_retraction
    X K N U P hstrict _eK
  obtain ⟨s, hs⟩ := exists_strictlyPerfect_evaluation_local_section
    X K N U P hstrict _eK
  change R.map g ≫ r = 𝟙 _ at hr
  change s ≫ R.map g = 𝟙 _ at hs
  have hrs : r = s := by
    calc
      r = 𝟙 _ ≫ r := (Category.id_comp r).symm
      _ = (s ≫ R.map g) ≫ r := by rw [hs]
      _ = s ≫ (R.map g ≫ r) := Category.assoc _ _ _
      _ = s := by rw [hr, Category.comp_id]
  let e : R.obj (N ⊗ D) ≅ R.obj (H.obj (op K, N)) :=
    { hom := R.map g
      inv := r
      hom_inv_id := hr
      inv_hom_id := by rw [hrs]; exact hs }
  let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))) _ _
      (inferInstanceAs (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))) :=
    inferInstanceAs (Category.{w}
      (DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))
  obtain ⟨c⟩ := derivedInternalHom_restrict_open X.toRingedSpace U K N
  obtain ⟨d⟩ := @derivedInternalHom_obj_iso.{u, w} (Over U) _
    ((Opens.grothendieckTopology X.toRingedSpace).over U)
    (X.sheaf.over U) (inferInstanceAs
      (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))))
    (R.obj K) (R.obj N) P F inferInstance
    _eK.symm _eN.symm
  let b := c.symm ≪≫ d
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  refine ⟨e ≪≫ b ≪≫ (Q.mapIso (asIso f)).symm, b, ?_⟩
  change R.map g ≫ b.hom =
    (R.map g ≫ b.hom ≫ (Q.mapIso (asIso f)).inv) ≫ Q.map f
  simp only [Category.assoc, Functor.mapIso_inv, asIso_inv,
    ← Functor.map_comp, IsIso.inv_hom_id]
  rw [Q.map_id, Category.comp_id]

end AlgebraicGeometry
