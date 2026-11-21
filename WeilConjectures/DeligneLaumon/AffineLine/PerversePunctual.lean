/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Perverse

/-!
# Middle extensions have no punctual subobjects or quotients

The middle extension `(j_*M)[1]` of an irreducible lisse Weil sheaf `M` on a dense open of the
affine line has no nonzero punctual subobject
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_of_mono_middleExtension`) and no nonzero
punctual quotient (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_of_epi_middleExtension`)
in the curve perverse heart.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf `G` vanishes if the punctual object `G[0]` of the curve perverse heart does. -/
theorem isZero_of_isZero_punctualObj {G : WeilSheaf k₀ l X} {hG : G.support.Finite}
    (h : IsZero (punctualObj G hG)) : IsZero G :=
  ((homologySheaf (0 : ℤ)).map_isZero ((ObjectProperty.ι _).map_isZero h)).of_iso
    (WeilSheaf.toComplexCompHomologySheafIso.app G).symm

end WeilComplex

namespace WeilSheaf.LisseOnDenseOpen

open WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The middle extension `(j_*M)[1]` of an irreducible lisse sheaf `M` has no nonzero punctual
subobject in the curve perverse heart. This is the case `C = 𝔸¹` of the statement for a smooth
curve `C`: lisse sheaves on dense opens (`WeilSheaf.LisseOnDenseOpen`) are only set up on `𝔸¹`. -/
theorem isZero_of_mono_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) (G : WeilSheaf k₀ l (affineLine k₀))
    (hG : G.support.Finite)
    (f : punctualObj G hG ⟶ ⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩) [Mono f] :
    IsZero G := by
  obtain h | h := eq_zero_or_isIso_of_mono_middleExtension D hD (Iso.refl _) f
  · exact isZero_of_isZero_punctualObj (IsZero.of_mono_eq_zero f h)
  · exfalso
    have := isIso_hom_of_isIso f
    refine hD.2.1 (D.isZero_of_isZero_lowerStar ?_)
    let e : D.middleExtension ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ := Iso.refl _
    have h1 : IsZero D.directImage :=
      (isZero_homologySheaf_singleComplex (by norm_num) G).of_iso
        ((WeilComplex.homologySheafShiftToComplexIso D.directImage 1 (-1) (by norm_num)).symm ≪≫
          (homologySheaf (-1 : ℤ)).mapIso e.symm ≪≫
            (homologySheaf (-1 : ℤ)).mapIso (asIso f.hom).symm)
    exact h1.of_iso (Iso.refl _ : (WeilSheaf.lowerStar D.j).obj D.sheaf ≅ D.directImage)

/-- The middle extension `(j_*M)[1]` of a lisse sheaf `M` has no nonzero punctual quotient in the
curve perverse heart. This is the case `C = 𝔸¹` of the statement for a smooth curve `C`. -/
theorem isZero_of_epi_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (G : WeilSheaf k₀ l (affineLine k₀)) (hG : G.support.Finite)
    (f : (⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩ :
      curvePerverse.FullSubcategory) ⟶ punctualObj G hG) [Epi f] :
    IsZero G := by
  have hP := D.isCurvePerverse_middleExtension
  have hP0 : IsZero ((homologySheaf (0 : ℤ)).obj D.middleExtension) :=
    WeilSheaf.isZero_homologySheaf_shift_toComplex _ (by norm_num)
  have h0 : f.hom = 0 := (homologySheaf_map_bijective 0 hP.1.1
    fun a ha ↦ isZero_homologySheaf_singleComplex ha.ne G).1 (hP0.eq_of_src _ _)
  exact isZero_of_isZero_punctualObj
    (IsZero.of_epi_eq_zero f (ObjectProperty.hom_ext _ (h0.trans rfl)))

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
