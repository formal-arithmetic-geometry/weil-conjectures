/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Derived open adjunctions at corresponding opens of isomorphic schemes

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem unit_isIso_of_iso {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {K K' : C} (i : K ≅ K') :
    IsIso (adj.unit.app K) ↔ IsIso (adj.unit.app K') := by
  rw [← adj.unit.naturality_1 i]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

private theorem exists_adjunction_of_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (eU : C' ≌ D') (L : C ⥤ C') (M : D ⥤ D')
    (R : D' ⥤ D) (adj : M ⊣ R) (c : e.functor ⋙ M ≅ L ⋙ eU.functor) :
    ∃ (S : C' ⥤ C) (adjS : L ⊣ S),
      ∀ K, IsIso (adjS.unit.app (e.inverse.obj K)) ↔ IsIso (adj.unit.app K) := by
  let b := (e.toAdjunction.comp adj).comp eU.symm.toAdjunction
  let α : (e.functor ⋙ M) ⋙ eU.inverse ≅ L :=
    isoWhiskerRight c eU.inverse ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft L eU.unitIso.symm ≪≫ Functor.rightUnitor _
  let a := b.ofNatIsoLeft α
  refine ⟨_, a, ?_⟩
  intro K
  have h : IsIso (a.unit.app (e.inverse.obj K)) ↔
      IsIso (adj.unit.app (e.functor.obj (e.inverse.obj K))) := by
    dsimp only [a, b]
    simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, whiskerRight_app,
      Adjunction.comp_unit_app]
    simp only [isIso_comp_left_iff, isIso_comp_right_iff,
      isIso_iff_of_reflects_iso]
  exact h.trans (unit_isIso_of_iso adj (e.counitIso.app K))

set_option backward.isDefEq.respectTransparency false in
/-- Open restriction has derived right adjoints whose units correspond under any
derived equivalence specified by isomorphism pushforward. -/
theorem exists_scheme_iso_derived_open_adjunction {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (U : Y.Opens) :
    ∃ (RX : DerivedCategory (SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (s.hom ⁻¹ᵁ U))) ⥤ schemeDerivedCategory X)
      (RY : DerivedCategory (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over U)) ⥤ schemeDerivedCategory Y)
      (adjX : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (s.hom ⁻¹ᵁ U)).mapDerivedCategory ⊣ RX)
      (adjY : (SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory ⊣ RY),
      ∀ K, IsIso (adjX.unit.app (e.inverse.obj K)) ↔ IsIso (adjY.unit.app K)  := by
  obtain ⟨eU, ⟨c⟩⟩ := exists_scheme_iso_derived_restriction_square s e he U
  let L := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let : L.IsLeftAdjoint := by dsimp [L, SheafOfModules.overFunctor]; infer_instance
  let R := Functor.rightAdjoint L
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  let : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      ((Opens.grothendieckTopology Y).over U)
      (Y.toRingedSpace.sheaf.over U)).1
  let adj := (Adjunction.ofIsLeftAdjoint L).mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨RX, adjX, h⟩ := exists_adjunction_of_square e eU
    (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (s.hom ⁻¹ᵁ U)).mapDerivedCategory
    L.mapDerivedCategory R.rightDerivedFunctor adj c
  exact ⟨RX, R.rightDerivedFunctor, adjX, adj, h⟩

end AlgebraicGeometry.Scheme
