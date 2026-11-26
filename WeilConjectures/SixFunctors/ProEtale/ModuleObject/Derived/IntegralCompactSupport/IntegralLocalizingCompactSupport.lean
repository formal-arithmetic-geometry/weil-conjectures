/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralNormalizedComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompatibleComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCartesianCompactSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportPullback

/-! # Integral compact support on the ordinary localizing category -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

/-- The integral compactly supported direct image restricts to an exact, coproduct
preserving functor on Loc(Dbc), carries Dbc into Dbc, and has normalized compactification,
composition and base-change isomorphisms, restricting to those same constructible objects. -/
theorem integralLocalizingCompactSupport (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    ∃ (h : Preservation (Profinite.padicIntegersRingObj ℓ E.val) k)
      (φ : Comparisons (Profinite.padicIntegersRingObj ℓ E.val) k)
      (μ : Compositions (Profinite.padicIntegersRingObj ℓ E.val) k),
      Coherence (Profinite.padicIntegersRingObj ℓ E.val) k h φ μ := by
  obtain ⟨φ, hi, hc, hn⟩ := normalizedComparisons k ℓ E
  have h := preservation_of_ctf_eq k ℓ E
  obtain ⟨μ, hm⟩ := compatibleComposition k ℓ E h φ hi hc hn
  have hp := fun {X Y : Spaces k} (v : X ⟶ Y) ↦ pullback_of_ctf_eq k ℓ E v
  obtain ⟨hb, hbc⟩ := cartesianCompactSupport k ℓ E h φ hi hc hn
    (fun v ↦ (hp v).2)
  exact ⟨h, φ, μ, ⟨hi, hc, hn, hm, fun v ↦ (hp v).1,
    fun v ↦ (hp v).2, hb, hbc⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
