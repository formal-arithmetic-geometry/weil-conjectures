/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The projection formula for a bounded second argument

Let `Λ` be a finite ring, `g : Z ⟶ Y` a proper morphism and `j : U ⟶ Z` an open immersion. For
`K` in `Dᵇctf(U_proét, Λ)` and `L` a bounded complex of étale origin on `Y` (not necessarily of
finite Tor amplitude), the projection map `Rg_*(j_! K) ⊗ᴸ L ⟶ Rg_*(j_! K ⊗ᴸ Lg^* L)` is an
isomorphism. As in `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_comparison`
this is the étale projection formula transported along `ν^*`; the boundedness of
`j_! K ⊗ᴸ Lg^* L` now comes from the finite Tor amplitude of `K` rather than of `L`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Coefficients

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Extension by zero along an open immersion `j : U ⟶ X` preserves Tor amplitude in `[a, b]`
on the pro-étale site: `j_!K ⊗ᴸ F ≅ j_!(K ⊗ᴸ j^*F)` by the projection formula, and `j_!` and
`j^*` are exact. -/
lemma torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    [ProEtale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)}
    (hK : DerivedCategory.torAmplitudeIn A U a b K) :
    DerivedCategory.torAmplitudeIn A X a b (D((j)_!open[A]).obj K) := fun G ↦ by
  let F := (j)_!open[A]
  -- `j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)`
  have e := (((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app
    ((_root_.DerivedCategory.singleFunctor _ 0).obj G)).symm ≪≫
    F.mapDerivedCategory.mapIso (((-⊗ᴸ-(U)[A]).obj K).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso A j).app G))
  obtain ⟨h₁, h₂⟩ := F.homologyConcentratedIn_mapDerivedCategory_obj (hK ((j)^*[A].obj G))
  have : _root_.DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
      (((-⊗ᴸ-(U)[A]).obj K).obj (((j)^*[A] ⋙
        _root_.DerivedCategory.singleFunctor _ 0).obj G))) a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE (F.mapDerivedCategory.obj
      (((-⊗ᴸ-(U)[A]).obj K).obj (((j)^*[A] ⋙
        _root_.DerivedCategory.singleFunctor _ 0).obj G))) b := h₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- Let `g : Z ⟶ Y`, let `M₀` and `L₀` be complexes of étale sheaves on `Z` and `Y` whose
pro-étale realizations `N ≅ ν^* M₀` and `L ≅ ν^* L₀` are respectively of finite Tor amplitude
and bounded. Then `M₀ ⊗ᴸ Lg^* L₀` is bounded below: its pro-étale realization is
`N ⊗ᴸ Lg^* L`, which is bounded since `N` has finite Tor amplitude and `Lg^* L` is bounded.
This is the variant of
`AlgebraicGeometry.ProEtale.plus_derivedTensor_leftDerivedUpperStar_of_comparison` with the
roles of the boundedness and of the Tor amplitude exchanged. -/
lemma plus_derivedTensor_leftDerivedUpperStar_of_comparison_of_torAmplitudeIn
    [Etale.UpperStarPreservesFlat A] [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {M₀ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (eM : N ≅ L(ν^*(Z)[A]).obj M₀) (eL : L ≅ L(ν^*(Y)[A]).obj L₀) {a b : ℤ}
    (hN : DerivedCategory.torAmplitudeIn A Z a b N)
    (hL : _root_.DerivedCategory.TStructure.t.bounded L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) := by
  let P := (L(ProEtale.upperStar A g)).obj L
  have hP : _root_.DerivedCategory.TStructure.t.bounded P :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory A g).app L).symm
      ((ProEtale.upperStar A g).bounded_mapDerivedCategory_obj hL)
  obtain ⟨p, q, hPpq⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded P).2 hP
  have hNP := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hN hPpq
  let e : D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) ≅ N ⊗ P :=
    ((ν^*(Z)[A]).leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
      asIso (((ν^*(Z)[A]).leftDerivedTensorComparison.app M₀).app _) ≪≫
      tensorIso eM.symm (((leftDerivedComparisonUpperStarCompUpperStarIso A g).app L₀).symm ≪≫
        (L(ProEtale.upperStar A g)).mapIso eL.symm)
  have hb : _root_.DerivedCategory.TStructure.t.bounded (D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀))) :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm
      ((_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1 ⟨_, _, hNP⟩)
  exact ((ν^*(Z)[A]).bounded_of_bounded_mapDerivedCategory_obj hb).1

end Coefficients

end AlgebraicGeometry.ProEtale
