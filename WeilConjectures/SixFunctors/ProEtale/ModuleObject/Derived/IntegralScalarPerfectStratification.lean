/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StratifiedScalarPerfectGeneration
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison

/-! # Integral local models as scalar-perfect stratifications -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The integral criterion's finite-free point models give a scalar-perfect stratification.
Source: blueprint internal-Hom stability proof, paragraph 1, integral coefficient case;
blueprint integral criterion, condition (3)
(blueprint: lem-sfb-integral-scalar-perfect-stratification).

Proof: take condition (3) of the four-way integral criterion. It gives a single finite
stratification and, on each stratum, a pro-etale cover and a bounded finite-free complex
on the condensed point. A finite-free module is its own finite-free retract. The exact
pullback composition comparison converts restriction along the composite chart-to-X map
to the two successive restrictions. The integral realization is by definition termwise
point pullback followed by localization. The empty scheme and rank-zero terms require
no separate choice. -/
theorem integral_scalarPerfectStratification
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (supportModules (DerivedNakayama.integerRing ℓ E) X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) X K) :
    HasScalarPerfectStratification (DerivedNakayama.integerRing ℓ E) X K := by
  let Λ := DerivedNakayama.integerRing ℓ E
  obtain ⟨s, hs⟩ := ((condensed_integral_criterion ℓ E X K).out 0 2).mp hK
  refine ⟨s, fun a ↦ ?_⟩
  obtain ⟨U, hU⟩ := hs a
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨F, b, c, hb, hc, hF, ⟨eF⟩⟩ := hU i
  refine ⟨F, ⟨b, c, fun n hn ↦ ?_⟩, ?_, inferInstance, ⟨?_⟩⟩
  · rcases hn with hn | hn
    · exact (CochainComplex.isStrictlyGE_iff F b).mp hb n hn
    · exact (CochainComplex.isStrictlyLE_iff F c).mp hc n hn
  · intro n
    obtain ⟨m, ⟨e⟩⟩ := hF n
    exact ⟨m, e.hom, e.inv, e.hom_inv_id⟩
  · exact ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarComp Λ (U.f i) (s.immersion a)).symm).app K
      ≪≫ eF

end AlgebraicGeometry.ProEtale.CondensedRing
