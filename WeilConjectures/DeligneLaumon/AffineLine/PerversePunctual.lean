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
in the curve perverse heart. (blueprint: `lemma-simple-objects--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf placed in degree `0` has vanishing cohomology sheaves outside degree `0`. -/
theorem isZero_homologySheaf_toComplex_obj (G : WeilSheaf k₀ l X) {a : ℤ} (ha : a ≠ 0) :
    IsZero ((homologySheaf a).obj (WeilSheaf.toComplex.obj G)) := by
  refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_
  change IsZero ((_root_.DerivedCategory.homologyFunctor _ a).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))
  obtain ha | ha := ha.lt_or_gt
  · exact (_root_.DerivedCategory.isGE_iff _ 0).1 inferInstance a ha
  · exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance a ha

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
subobject in the curve perverse heart: a subobject is `0` or everything
(`AlgebraicGeometry.WeilComplex.eq_zero_or_isIso_of_mono_middleExtension`), and `(j_*M)[1]` is
not punctual, its `𝓗⁻¹ = j_*M` being nonzero. (blueprint: `lemma-simple-objects--2`) -/
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
      (isZero_homologySheaf_toComplex_obj G (by norm_num : (-1 : ℤ) ≠ 0)).of_iso
        ((WeilComplex.homologySheafShiftToComplexIso D.directImage 1 (-1) (by norm_num)).symm ≪≫
          (homologySheaf (-1 : ℤ)).mapIso e.symm ≪≫
            (homologySheaf (-1 : ℤ)).mapIso (asIso f.hom).symm)
    exact h1.of_iso (Iso.refl _ : (WeilSheaf.lowerStar D.j).obj D.sheaf ≅ D.directImage)

/-- The middle extension `(j_*M)[1]` of a lisse sheaf `M` has no nonzero punctual quotient in the
curve perverse heart: `(j_*M)[1]` is concentrated in degree `-1` and a punctual object in degree
`0`, so every morphism from the former to the latter vanishes.
(blueprint: `lemma-simple-objects--2`) -/
theorem isZero_of_epi_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (G : WeilSheaf k₀ l (affineLine k₀)) (hG : G.support.Finite)
    (f : (⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩ :
      curvePerverse.FullSubcategory) ⟶ punctualObj G hG) [Epi f] :
    IsZero G := by
  have hP := D.isCurvePerverse_middleExtension
  have hP0 : IsZero ((homologySheaf (0 : ℤ)).obj D.middleExtension) :=
    WeilSheaf.isZero_homologySheaf_shift_toComplex _ (by norm_num)
  have h0 : f.hom = 0 := (homologySheaf_map_bijective 0 hP.1.1
    fun a ha ↦ isZero_homologySheaf_toComplex_obj G ha.ne).1 (hP0.eq_of_src _ _)
  exact isZero_of_isZero_punctualObj
    (IsZero.of_epi_eq_zero f (ObjectProperty.hom_ext _ (h0.trans rfl)))

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
