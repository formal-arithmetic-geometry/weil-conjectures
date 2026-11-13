/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.SupportedAffineOverlapMap
public import WeilConjectures.AlgebraicGeometry.SupportedRelativeOpenGluing
public import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationData

/-! # Supported perfect gluing on the union with an affine open

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relative_restriction_comp_iso
    (X : Scheme.{u}) (U W Y : X.Opens) (hUW : U ≤ W) (hWY : W ≤ Y) :
    schemeOpenOverlapRestriction X (homOfLE hWY) ⋙
      schemeOpenOverlapRestriction X (homOfLE hUW) ≅
    schemeOpenOverlapRestriction X (homOfLE (le_trans hUW hWY)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Modules.overEquiv Y).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWY))
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (Modules.overEquiv W).unitIso.symm _ ≪≫
              Functor.leftUnitor _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Iso.refl (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (le_trans hUW hWY))))
          (Modules.overEquiv U).functor)

private theorem stabilized_map_restriction
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [Preadditive A] [Preadditive B] [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    [HasShift A ℤ] [HasShift B ℤ]
    (L : C ⥤ D) (H : D ⥤ B) (J : C ⥤ B) (JW : C ⥤ A)
    (P : D ⥤ A) (Q : A ⥤ B) [Q.Additive] [Q.CommShift ℤ]
    (d : H ≅ P ⋙ Q) (kW : L ⋙ P ≅ JW) (kU : JW ⋙ Q ≅ J) (c : L ⋙ H ≅ J)
    (E R : C) (β : R ⟶ E) (F : D) (α : F ⟶ L.obj E)
    (iW : P.obj F ≅ JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧)
    (hα : P.map α ≫ kW.hom.app E = iW.hom ≫ biprod.fst ≫ JW.map β) :
    ∃ e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧,
      H.map α ≫ c.hom.app E = e.hom ≫ biprod.fst ≫ J.map β := by
  have : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  let k : L ⋙ H ≅ J :=
    Functor.isoWhiskerLeft L d ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight kW Q ≪≫ kU
  let e₀ : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧ :=
    d.app F ≪≫ Q.mapIso iW ≪≫ Q.mapBiprod (JW.obj R) ((JW.obj R)⟦(1 : ℤ)⟧) ≪≫
      biprod.mapIso (kU.app R)
        ((Q.commShiftIso (1 : ℤ)).app (JW.obj R) ≪≫
          (shiftFunctor _ (1 : ℤ)).mapIso (kU.app R))
  have he₀ : H.map α ≫ k.hom.app E = e₀.hom ≫ biprod.fst ≫ J.map β := by
    have hk : k.hom.app E = d.hom.app (L.obj E) ≫ Q.map (kW.hom.app E) ≫
        kU.hom.app E := by simp [k]
    rw [hk, ← Category.assoc, ← Category.assoc, d.hom.naturality α]
    simp only [Functor.comp_map, Category.assoc]
    rw [← Q.map_comp_assoc, hα, Q.map_comp]
    simp only [e₀, Iso.trans_hom, Functor.mapIso_hom, Functor.mapBiprod_hom,
      biprod.mapIso_hom, Category.assoc, biprod.map_fst_assoc, biprod.lift_fst_assoc]
    simp only [Q.map_comp, Category.assoc]
    have hu := kU.hom.naturality β
    simp only [Functor.comp_map] at hu
    rw [hu]
    rfl
  let t : J ≅ J := k.symm ≪≫ c
  let e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧ :=
    e₀ ≪≫ biprod.mapIso (t.app R) ((shiftFunctor _ (1 : ℤ)).mapIso (t.app R))
  refine ⟨e, ?_⟩
  calc
    H.map α ≫ c.hom.app E = (H.map α ≫ k.hom.app E) ≫ t.hom.app E := by simp [t]
    _ = (e₀.hom ≫ biprod.fst ≫ J.map β) ≫ t.hom.app E := by rw [he₀]
    _ = e₀.hom ≫ biprod.fst ≫ t.hom.app R ≫ J.map β := by
      rw [Category.assoc, Category.assoc, ← t.hom.naturality β]
    _ = e.hom ≫ biprod.fst ≫ J.map β := by
      simp only [e, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
        biprod.map_fst_assoc, Iso.app_hom]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- Derived composition comparisons and their additivity instances require this budget.
/-- The affine construction produces a perfect supported source on the union itself.
There is no ambient extension in this statement. The supplied natural comparison `c`
identifies iterated restriction through the union with direct restriction to `U`. -/
theorem exists_supported_map_affine_union_gluing
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (U W V : X.Opens) (hUW : U ≤ W) (hW : IsCompact (W : Set X))
    (hV : IsAffineOpen V) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [∀ O : (W ⊔ V).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (W ⊔ V).toScheme.toRingedSpace).over O))]
    (E : schemeDerivedQCohCategory X)
    (R : schemeDerivedCategory X) (β : R ⟶ E.obj)
    (hR : (∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)))
    (hRT : (∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x)))) :
    let Y := W ⊔ V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Y ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y)
    let H := Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y) ⋙
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (le_trans hUW le_sup_left)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    let J := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    ∀ c : L.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ J.mapDerivedCategory,
    ∃ (F : schemeDerivedCategory Y.toScheme) (α : F ⟶ L.mapDerivedCategory.obj E.obj),
      IsPerfect Y.toScheme F ∧
      (∀ (i : ℤ) (x : Y.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace)) i).obj F).val.presheaf x))) ∧
      ∃ e : H.mapDerivedCategory.obj F ≅
          J.mapDerivedCategory.obj R ⊞ (J.mapDerivedCategory.obj R)⟦(1 : ℤ)⟧,
        H.mapDerivedCategory.map α ≫ c.hom.app E.obj =
          e.hom ≫ biprod.fst ≫ J.mapDerivedCategory.map β := by
  classical
  let Y := W ⊔ V
  let L := (schemeOpenRestriction X Y).mapDerivedCategory
  let H := (schemeOpenOverlapRestriction X
    (homOfLE (le_trans hUW le_sup_left) : U ⟶ Y)).mapDerivedCategory
  let J := (schemeOpenRestriction X U).mapDerivedCategory
  change ∀ c : L ⋙ H ≅ J,
    ∃ (F : schemeDerivedCategory Y.toScheme) (α : F ⟶ L.obj E.obj),
      IsPerfect Y.toScheme F ∧
      (∀ (i : ℤ) (x : Y.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace)) i).obj F).val.presheaf
            x))) ∧
      ∃ e : H.obj F ≅ J.obj R ⊞ (J.obj R)⟦(1 : ℤ)⟧,
        H.map α ≫ c.hom.app E.obj = e.hom ≫ biprod.fst ≫ J.map β
  intro c
  obtain ⟨hDW, ⟨hOW⟩⟩ := open_derived_localization_data X W
  let := hDW
  let := hOW
  obtain ⟨hDV, ⟨hOV⟩⟩ := open_derived_localization_data X V
  let := hDV
  let := hOV
  obtain ⟨hDI, ⟨hOI⟩⟩ := open_derived_localization_data X (W ⊓ V)
  let := hDI
  let := hOI
  let JW := (schemeOpenRestriction X W).mapDerivedCategory
  let P := (schemeOpenOverlapRestriction X
    (homOfLE le_sup_left : W ⟶ Y)).mapDerivedCategory
  let Q := (schemeOpenOverlapRestriction X (homOfLE hUW : U ⟶ W)).mapDerivedCategory
  let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ Y)
  let kU := schemeDerivedOpenRestrictionCompIso X (homOfLE hUW : U ⟶ W)
  let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
  obtain ⟨hA, hAT, B, b, s, hB, hBT, hs⟩ :=
    exists_supported_affine_overlap_map X W V hW hV T hT hTc E R β hR hRT
  obtain ⟨F, α, hF, hFT, iW, _iV, hα, _hαV⟩ :=
    exists_supported_relative_open_gluing X W V T A B hA hB hAT hBT
      s E.obj (biprod.fst ≫ JW.map β) b hs
  let d : H ≅ P ⋙ Q :=
    (Functor.mapDerivedCategoryNatIso
      (relative_restriction_comp_iso X U W Y hUW le_sup_left)).symm ≪≫
      (Functor.mapDerivedCategoryCompIso
        (schemeOpenOverlapRestriction X (homOfLE le_sup_left : W ⟶ Y))
        (schemeOpenOverlapRestriction X (homOfLE hUW : U ⟶ W))).symm
  have : Q.Additive := inferInstance
  obtain ⟨e, he⟩ := stabilized_map_restriction L H J JW P Q d kW kU c
    E.obj R β F α iW hα
  exact ⟨F, α, hF, hFT, e, he⟩

end AlgebraicGeometry.Scheme
