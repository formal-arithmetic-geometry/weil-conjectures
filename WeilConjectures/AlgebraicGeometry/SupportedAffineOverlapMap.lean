/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.SupportedOverlapPerfectExtension
import WeilConjectures.AlgebraicGeometry.LocalPerfectSupportedStabilization
import WeilConjectures.AlgebraicGeometry.CompactOverlapRestrictionModel
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Supported affine overlap data

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem map_lift_transport
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (S : C ⥤ H) (e : D ≌ H) (d : L ⋙ e.functor ≅ S)
    {Q B E : C} (α : S.obj Q ⟶ S.obj E) (bU : L.obj B ≅ L.obj Q)
    (b : B ⟶ E)
    (h : e.functor.preimage (d.hom.app Q ≫ α ≫ d.inv.app E) = bU.inv ≫ L.map b) :
    α = ((d.app Q).inv ≫ e.functor.map bU.inv ≫ (d.app B).hom) ≫ S.map b := by
  have hh := congrArg e.functor.map h
  rw [Functor.map_preimage, Functor.map_comp] at hh
  have hn := d.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  calc
    α = d.inv.app Q ≫ (d.hom.app Q ≫ α ≫ d.inv.app E) ≫ d.hom.app E := by
      simp only [Category.assoc, d.inv_hom_id_app_assoc, d.inv_hom_id_app,
        Category.comp_id]
    _ = d.inv.app Q ≫ (e.functor.map bU.inv ≫ e.functor.map (L.map b)) ≫
        d.hom.app E := by rw [hh]
    _ = _ := by
      simp only [Category.assoc]
      rw [hn]
      rfl

set_option maxHeartbeats 800000 in
-- Derived restriction transport elaborates across several chosen localizations.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the affine member and its compatible overlap map; no object on the union
is asserted. -/
theorem exists_supported_affine_overlap_map
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ O : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
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
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
    let a : A ⟶ JW.obj E.obj := biprod.fst ≫ JW.map β
    IsPerfect W.toScheme A ∧
      (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj A).val.presheaf x))) ∧
      ∃ (B : schemeDerivedCategory V.toScheme) (b : B ⟶ JV.obj E.obj)
        (c : SW.obj A ≅ SV.obj B),
        IsPerfect V.toScheme B ∧
        (∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj B).val.presheaf
              x))) ∧
        SW.map a ≫ kW.hom.app E.obj = c.hom ≫ SV.map b ≫ kV.hom.app E.obj := by
  classical
  let JW := (schemeOpenRestriction X W).mapDerivedCategory
  let JV := (schemeOpenRestriction X V).mapDerivedCategory
  let SW := (schemeOpenOverlapRestriction X
    (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
  let SV := (schemeOpenOverlapRestriction X
    (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
  let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
  let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
  let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
  let a : A ⟶ JW.obj E.obj := biprod.fst ≫ JW.map β
  obtain ⟨hF, hFT, hA, hAT⟩ := local_perfect_supported_stabilization X W T R hR hRT
  obtain ⟨Q, hQ, hQT, ⟨q⟩⟩ :=
    exists_supported_overlap_perfect_extension X W V hW hV T hT hTc (JW.obj R) hF hFT
  obtain ⟨U, hU, hD, e, ⟨d⟩⟩ :=
    exists_compact_overlap_restriction_model X W V hW hV
  let := hD
  let : IsAffine V.toScheme := hV
  let L := (schemeOpenRestriction V.toScheme U).mapDerivedCategory
  let EV : schemeDerivedQCohCategory V.toScheme := ⟨JV.obj E.obj, by
    apply (schemeDerivedQCoh_openRestriction_iff X V E.obj).mpr
    intro n
    have := E.property n
    exact SheafOfModules.isQuasicoherent_over _ V⟩
  let α : SV.obj Q ⟶ SV.obj EV.obj :=
    q.hom ≫ SW.map a ≫ kW.hom.app E.obj ≫ kV.inv.app E.obj
  let α₀ : L.obj Q ⟶ L.obj EV.obj :=
    e.functor.preimage (d.hom.app Q ≫ α ≫ d.inv.app EV.obj)
  obtain ⟨B, I, δ, b, hB, _hI, _hδ, ⟨bU, _hbU, hα₀⟩, hBT⟩ :=
    exists_perfect_map_lift_of_isAffine V.toScheme U hU EV Q hQ α₀
  let bS : SV.obj B ≅ SV.obj Q :=
    (d.app B).symm ≪≫ e.functor.mapIso bU ≪≫ d.app Q
  have hα : α = bS.inv ≫ SV.map b := by
    simpa only [bS, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
      using map_lift_transport L SV e d α bU b hα₀
  refine ⟨hA, hAT, B, b, q.symm ≪≫ bS.symm, hB, ?_, ?_⟩
  · exact hBT (Subtype.val ⁻¹' T) (hT.preimage continuous_subtype_val) hQT
  · change SW.map a ≫ kW.hom.app E.obj =
      (q.inv ≫ bS.inv) ≫ SV.map b ≫ kV.hom.app E.obj
    calc
      SW.map a ≫ kW.hom.app E.obj = q.inv ≫ α ≫ kV.hom.app E.obj := by
        dsimp only [α]
        simp only [Category.assoc, q.inv_hom_id_assoc, kV.inv_hom_id_app,
          Category.comp_id]
      _ = _ := by rw [hα]; simp only [Category.assoc]

end AlgebraicGeometry.Scheme
