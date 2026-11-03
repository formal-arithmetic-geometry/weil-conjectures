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
