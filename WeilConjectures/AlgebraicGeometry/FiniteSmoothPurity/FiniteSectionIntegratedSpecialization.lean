/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import all WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecializationIntegrationBaseChange

/-! # Integrated section specialization with arbitrary finite coefficients

Source: latest blueprint, smooth-purity base-change factors, proof (1).
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

section Section
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {V S : Scheme.{u}} [IsNoetherian S]
variable (d : ℕ) (g : V ⟶ S)
variable (s : S ⟶ V) [IsClosedImmersion s]
variable [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
variable (sq : IsPullback
  ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
  (Scheme.Hom.normalConeProj g s)
  (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))

variable [HasCompactification g]

end Section

end FiniteSmoothPurity
end Etale
end AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The cone-to-bundle section map is invertible, since its horizontal map is an
isomorphism and the bundle projection is smooth.
Source: finite smooth orientation normalization, normal-bundle factor
(blueprint: lem-sp-finite-section-integrated-specialization-base-change). -/
theorem normalSectionMap_isIso (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) : IsIso (normalSectionMap A d g s hs sq) := by
  let q := reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s
  have hq : q.hom ≫ VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1) = Scheme.Hom.normalConeProj g s := by
    simpa only [Category.comp_id] using sq.w
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  let π := VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)
  have : SmoothOfRelativeDimension d π := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension d) q.hom π).mp
    rw [hq]
    infer_instance
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  have : HasInvertibleExponent A (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) := HasInvertibleExponent.of_hom π
  let := (vectorBundlePurityCompactification S d
    (ConormalGradedAlgebra.piece s 1)).hasCompactification
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension A π d sq
  have : IsIso (dualizingComplexBaseChangeMap A sq) :=
    (isIso_dualizingComplexBaseChangeMap_iff A sq).2 inferInstance
  unfold normalSectionMap NoetherianSectionSpecialization.sectionMap
  infer_instance

end AlgebraicGeometry.Etale.FiniteSmoothPurity
