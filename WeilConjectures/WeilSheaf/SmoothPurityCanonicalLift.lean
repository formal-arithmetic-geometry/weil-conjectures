/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.OrientationCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-! # Reconstruction of the canonical integral smooth orientation

The prescribed finite orientations lift once they commute with the actual reduction
transitions. Derived Nakayama makes every such lift invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- A lift of the canonical finite orientations is invertible already modulo `ℓ`. -/
theorem isIso_of_isIntegralSmoothOrientation
    (φ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))
    (hφ : IsIntegralSmoothOrientation ℓ E f d φ) : IsIso φ := by
  apply isIso_of_isIso_etaleReduction_map ℓ E.1 one_ne_zero φ
  change IsIso ((finiteEtaleReading ℓ E.1 1 X).map
    ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map φ))
  rw [hφ 0]
  infer_instance

/-- A rational orientation with the specified integral normalization is invertible. -/
theorem isIso_of_isCanonicalSmoothOrientation
    (φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (hφ : IsCanonicalSmoothOrientation ℓ f d φ) : IsIso φ := by
  obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
  have := isIso_of_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ hφ₀
  infer_instance

/-- The canonical finite orientation, transported back from the fully faithful étale reading. -/
noncomputable def canonicalFiniteIntegralOrientationIso (n : ℕ) :
    (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)) ≅
      (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :=
  (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).preimageIso
    ((finiteEtaleReading ℓ E.1 n X).mapIso
        (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 n X.left _ (2 * d : ℤ)) ≪≫
      ((finiteEtaleReading ℓ E.1 n X).commShiftIso (2 * d : ℤ)).app _ ≪≫
      etaleReductionSmoothOrientationIso ℓ E f d n)

@[reassoc]
lemma canonicalFiniteIntegralOrientationIso_map_hom (n : ℕ) :
    (finiteEtaleReading ℓ E.1 n X).map
        (canonicalFiniteIntegralOrientationIso ℓ E f d n).hom =
      (finiteEtaleReading ℓ E.1 n X).map
          (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 n X.left _
            (2 * d : ℤ)).hom ≫
        ((finiteEtaleReading ℓ E.1 n X).commShiftIso (2 * d : ℤ)).hom.app _ ≫
          (etaleReductionSmoothOrientationIso ℓ E f d n).hom := by
  exact (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).map_preimage _

/-- The same prescribed orientation in the ambient derived category of the reduction. -/
noncomputable def canonicalAmbientIntegralOrientationIso (n : ℕ) :
    (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)).obj ≅
      (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)).obj :=
  ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 n).app
      ((shiftFunctor _ (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))).symm ≪≫
    (boundedConstructible (condensedRingObj
      (Profinite.integersModPowRingObj ℓ E.1 n) X.left)).ι.mapIso
        (canonicalFiniteIntegralOrientationIso ℓ E f d n) ≪≫
      (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 n).app
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))

/-- Compatibility with the actual reduction transitions is the sole reconstruction input. -/
def CanonicalIntegralOrientationCompatible : Prop :=
  ∀ n : ℕ,
    (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1 + 1))).mapDerivedCategory.map
        (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      reductionTransition E.1 (n + 1)
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)).obj =
    reductionTransition E.1 (n + 1)
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)).obj ≫
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.map
        (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1)).hom

/-- Reconstruct the prescribed finite orientations, with their normalization intact. -/
theorem exists_isIntegralSmoothOrientation_of_compatible
    (h : CanonicalIntegralOrientationCompatible ℓ E f d) :
    ∃ φ, IsIntegralSmoothOrientation ℓ E f d φ := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let K := (shiftFunctor _ (2 * d : ℤ)).obj
    (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
    X.left)).ι
  obtain ⟨φ, hφ⟩ := exists_derivedReduction_map_eq
    (K := K.obj) (derivedCompleteIntegers_of_boundedConstructible W.property)
    (fun n ↦ (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1)).hom) h
  let g : K ⟶ W := (ObjectProperty.fullyFaithfulι _).preimage φ
  have hg : ι.map g = φ := (ObjectProperty.fullyFaithfulι _).map_preimage _
  refine ⟨g, fun n ↦ ?_⟩
  have hr : (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map g =
      (canonicalFiniteIntegralOrientationIso ℓ E f d (n + 1)).hom := by
    apply (ObjectProperty.fullyFaithfulι _).map_injective
    apply (cancel_mono
      ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1
        (n + 1)).hom.app W)).mp
    rw [(boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1
      (n + 1)).hom.naturality g]
    change _ = _
    rw [hg, hφ n]
    simp only [canonicalAmbientIntegralOrientationIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hr]
  exact canonicalFiniteIntegralOrientationIso_map_hom ℓ E f d (n + 1)

/-- The integral reconstruction supplies an invertible canonical rational orientation. -/
theorem exists_isIso_isCanonicalSmoothOrientation_of_compatible
    (h : CanonicalIntegralOrientationCompatible ℓ ⟨⊥, inferInstance⟩ f d) :
    ∃ φ, IsIso φ ∧ IsCanonicalSmoothOrientation ℓ f d φ := by
  obtain ⟨φ₀, hφ₀⟩ := exists_isIntegralSmoothOrientation_of_compatible ℓ
    ⟨⊥, inferInstance⟩ f d h
  have := isIso_of_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ hφ₀
  exact ⟨extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀,
    inferInstance, φ₀, hφ₀, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
