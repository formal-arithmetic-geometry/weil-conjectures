/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexCompatibility

/-! # Termwise coefficient complex construction

This algebraic construction works for any complex; boundedness and the choice of a
representative in the derived category are handled in the presentation theorem.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

/-- Termwise scalar extension and restriction give the coefficient colimit diagram.

Source: archived master `ModuleObject/Colimit/TwoColimit.lean`, Hom paragraph,
and the coefficient construction in step 3 of
`prop-weil-pbc-qbar-condensed-two-colimit`. -/
theorem exists_condensed_coefficient_complex_model
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : FiniteIntermediateField ℓ)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ FiniteIntermediateField ℓ) [H.Final]
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    ∃ N : I ⥤ CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ,
      ∃ c : Cocone N, Nonempty (IsColimit c) ∧
      (∀ i, N.obj i =
        (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hf i))) ⋙
          Mod.comap (padicSubfieldRingObjMap X ℓ (he i))).mapHomologicalComplex
            (.up ℤ)).obj C) ∧
      ∃ eΩ : DerivedCategory.Q.obj c.pt ≅
          (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
            ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj (DerivedCategory.Q.obj C)),
        ∃ ei : ∀ i : I, DerivedCategory.Q.obj (N.obj i) ≅
            (finiteCoefficientDerivedRestriction X ℓ (he i)).obj
              ((derivedExtendScalarsSubfield X ℓ (hf i)).obj (DerivedCategory.Q.obj C)),
          ∀ i : I,
            finiteCoefficientDerivedAlgClHomEquiv X ℓ E
              (DerivedCategory.Q.obj (N.obj i)) _
              ((derivedExtendScalarsCompIso X ℓ (he i)).inv.app
                  (DerivedCategory.Q.obj (N.obj i)) ≫
                (derivedExtendScalarsToPadicAlgCl X ℓ (H.obj i)).map
                    ((finiteCoefficientDerivedHomEquiv X ℓ (he i)
                        (DerivedCategory.Q.obj (N.obj i)) _).symm (ei i).hom) ≫
                  (derivedExtendScalarsCompIso X ℓ (hf i)).hom.app
                    (DerivedCategory.Q.obj C)) =
              DerivedCategory.Q.map (c.ι.app i) ≫ eΩ.hom := by
  refine ⟨coefficientComplexDiagram X ℓ C H he hf,
    coefficientComplexCocone X ℓ C H he hf,
    nonempty_isColimit_coefficientComplexCocone X ℓ C H he hf, fun _ ↦ rfl,
    coefficientComplexVertexIso X ℓ C,
    (fun i ↦ coefficientComplexStageIso X ℓ (he i) (hf i) C), ?_⟩
  intro i
  exact coefficientComplexToAlgCl_derived_compatibility X ℓ (he i) (hf i) C

end AlgebraicGeometry.ProEtale
