/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension
import WeilConjectures.AlgebraicGeometry.SupportedOverlapRestrictionData

/-! # Supported perfect extension across an affine overlap

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The chosen overlap localization and its open-site family are dependent data.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Extend the stabilization of a supported perfect object from the overlap to V. -/
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

end AlgebraicGeometry.Scheme
