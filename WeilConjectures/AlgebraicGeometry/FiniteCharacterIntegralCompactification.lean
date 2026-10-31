/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Compactification.Affine
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.Etale

/-- Compactification transfer for ordinary finite-coefficient compact support over
an algebraically closed field. Over a field, any structural-field twist induced
by the open immersion is an automorphism and the compact-support comparison is
invariant under that twist.
Source: latest blueprint, `lem-fd-character-integral-finite`, proof Step 1.

Proof: proper/open compact-support comparison identifies the global sections of extension by
zero on a proper K-scheme with the compactly supported derived global sections of affine
r-space. The only possible mismatch in the chosen K-structure is induced by an automorphism
of the algebraically closed field K; transport along that automorphism preserves the zero
object. Refinement comparison and composition coherence then give the displayed result.
(blueprint: lem-fd-character-integral-finite-compactification-transfer) -/
theorem finite_character_integral_compactification_transfer
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : Type u) [Field K] [IsAlgClosed K] (r : ℕ)
    (F : Sheaf (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of K))).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : IsZero ((R(𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of K)) ↘
      Spec (CommRingCat.of K))_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)))
    (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of K))]
    (a : 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of K)) ⟶ Z) [IsOpenImmersion a]
    [IsProper (Z ↘ Spec (CommRingCat.of K))] :
    IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
      (((a)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
