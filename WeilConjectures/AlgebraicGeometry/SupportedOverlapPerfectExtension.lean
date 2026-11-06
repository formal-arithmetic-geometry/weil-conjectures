/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme


/-! # Supported perfect extension across an affine overlap

Source: Stacks Project, Tags 08EK and 09IM.
(blueprint: lem-sc-supported-overlap-perfect-extension).
-/

theorem exists_supported_overlap_perfect_extension
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (F : schemeDerivedCategory W.toScheme) (hF : IsPerfect W.toScheme F)
    (hFT : (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))) :
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    ∃ Q : schemeDerivedCategory V.toScheme, IsPerfect V.toScheme Q ∧
      (∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj Q).val.presheaf x))) ∧
      Nonempty (SV.obj Q ≅ SW.obj (F ⊞ F⟦(1 : ℤ)⟧)) := by
  classical
  obtain ⟨U, hU, hTV, hTVc, hD, hO, G, hG, hGT, e, ⟨d⟩, ⟨g⟩⟩ :=
    exists_supported_overlap_restriction_data X W V hW hV T hT hTc F hF hFT
  let := hD
  let := hO
  let : IsAffine V.toScheme := hV
  obtain ⟨Q, hQ, hQT, ⟨q⟩⟩ := exists_perfect_supported_extension V.toScheme
    (Subtype.val ⁻¹' T) hTV hTVc U hU G hG hGT
  exact ⟨Q, hQ, hQT, ⟨(d.app Q).symm ≪≫ e.functor.mapIso q ≪≫ g⟩⟩
