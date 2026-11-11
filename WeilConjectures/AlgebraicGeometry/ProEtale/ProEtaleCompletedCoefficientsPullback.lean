/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficients

/-!
# Compatibility of the completed-coefficient comparisons with inverse image

The comparisons `𝒪_{E,X} ≅ lim_n (𝒪_E/π_E^n)_X`, `E_X ≅ 𝒪_{E,X}[1/ℓ]` and
`Q̄_{ℓ,X} ≅ colim_E E_X` of `AlgebraicGeometry.ProEtale.sfb_completed_coefficients` are
compatible with inverse image along every morphism of schemes
(`AlgebraicGeometry.ProEtale.sfb_completed_coefficients_pullback`, blueprint
`lemma-comparison-completed-coefficients--4`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The inverse-image compatibility of the integral and rational comparisons for the integers
`R ⊆ K` with ideal `I`: the normalized integral limit cone `ρ` stays a limit cone after inverse
image along every morphism of schemes, and the legs `ι` of the rationalization colimit commute
with the inverse-image comparisons. The normalizations of `ρ` and `ι` are those of
`AlgebraicGeometry.ProEtale.SfbCompletedCoefficientComparison`. -/
def SfbCompletedCoefficientPullbackCompatible (ℓ : ℕ) (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) : Prop :=
  (∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
      sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
    (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
    (∀ X : Scheme.{u}, Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
      (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ)))) ∧
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
        ((upperStarFromPoint Y).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) ∧
  ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
      (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
    (∀ X : Scheme.{u}, ((ι X).app 0).hom = (i X).hom ∧
      Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X)))) ∧
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
      (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
          ((coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
        ((coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫
          ((ι X).app m).hom

/-- The integral and rational comparisons are compatible with inverse image. -/
theorem SfbCompletedCoefficientComparison.pullbackCompatible {ℓ : ℕ} {R K : Type} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {I : Ideal R}
    {i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))}
    (h : SfbCompletedCoefficientComparison.{u} ℓ R K I i) :
    SfbCompletedCoefficientPullbackCompatible.{u} ℓ R K I i := by
  obtain ⟨ρ, hρ, hX, hf, ι, hι, hιf, -⟩ := h
  exact ⟨⟨ρ, hρ, fun X ↦ (hX X).1, hf⟩, ι, fun X ↦ ⟨(hι X).1, (hι X).2.1⟩, hιf⟩

/-- The canonical isomorphisms `𝒪_{E,X} ≅ lim_n (𝒪_E/π_E^n)_X`, `E_X ≅ 𝒪_{E,X}[1/ℓ]` (for every
finite extension `E` of `ℚ_ℓ` inside `Q̄_ℓ`, and for `ℤ_ℓ ⊆ ℚ_ℓ`) and `Q̄_{ℓ,X} ≅ colim_E E_X`
are compatible with inverse image along every morphism of schemes `f : X ⟶ Y`: the pulled-back
integral limit cone is a limit cone, the rationalization legs commute with the inverse-image
comparisons, the pulled-back algebraic-closure cocone is a colimit cocone, and its legs commute
with the inverse-image comparisons.
(blueprint: `lemma-comparison-completed-coefficients--4`) -/
theorem sfb_completed_coefficients_pullback (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (π : PadicAlgCl.integers ℓ E),
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span ({π} : Set _) →
      SfbCompletedCoefficientPullbackCompatible.{u} ℓ (PadicAlgCl.integers ℓ E) E
        (Ideal.span ({π} : Set _))
        (fun X ↦ Mon.ofHom (padicIntegersToPadicSubfield X ℓ E))) ∧
    SfbCompletedCoefficientPullbackCompatible.{u} ℓ ℤ_[ℓ] ℚ_[ℓ]
      (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]))
      (sfbCoefficientInclusion ℤ_[ℓ] ℚ_[ℓ] PadicInt.Coe.ringHom
        continuous_subtype_val) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), Nonempty (IsColimit
      ((upperStar Ab.{u + 1} f).mapMon.mapCocone
        ((upperStarFromPoint Y).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ))))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (E : PadicAlgCl.FiniteIntermediateField ℓ),
      (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl Y ℓ E) ≫
          condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f =
        condensedPullbackHom (Profinite.continuousMapRingObj E) f ≫
          padicSubfieldRingObjToPadicAlgCl X ℓ E) := by
  obtain ⟨hE, hZ, -, -, hcolim, hnat⟩ := sfb_completed_coefficients.{u} ℓ
  exact ⟨fun E π hπ ↦ (hE E π hπ).pullbackCompatible, hZ.pullbackCompatible, hcolim, hnat⟩

end AlgebraicGeometry.ProEtale
