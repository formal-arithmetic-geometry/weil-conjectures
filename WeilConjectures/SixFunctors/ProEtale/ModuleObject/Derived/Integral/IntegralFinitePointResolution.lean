/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionAlgebraic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionContinuous

/-! # The finite integral coefficient point resolution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A finite discrete integral algebra has a two-term finite free point resolution. -/
theorem integralFinitePointResolution
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩)
    (ha : IsIntegralFiniteScalarMap ell E A a) :
    ∃ (P : ShortComplex (IntegralFiniteScalar.PointModules
        (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}))) (r : ℕ),
      P.ShortExact ∧
      Nonempty (P.X₁ ≅ biproduct
        (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
      Nonempty (P.X₂ ≅ biproduct
        (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
      Nonempty (P.X₃ ≅ (Mod.comap a.hom.hom).obj
      (Mod.regular (cartesianFinitePointRing A))) := by
      letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := discreteTopology_bot A
      letI : IsTopologicalRing A := inferInstance
      obtain ⟨φ, hφ, hsection⟩ := ha
      letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
      obtain ⟨r, f, g, hf, hfg, hg⟩ :=
        integralFinitePointResolution_algebraic ell E A hA φ
      obtain ⟨P, hP⟩ :=
        integralFinitePointResolution_continuous ell E A a φ hφ hsection r f g hf hfg hg
      exact ⟨P, r, hP⟩

end AlgebraicGeometry.ProEtale.CondensedRing
