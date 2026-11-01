/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteLevels

/-! # Complete integral coefficients and all finite reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- Integral finite constant models give canonical completeness and finite Tor bounds
at every positive reduction.
Source: blueprint integral criterion, (1) implies (2), and integral finite levels.
(blueprint: lem-per-integral-coefficient-hom-reductions)

Proof: Apply the integral criterion to obtain completeness and constructibility of the
first reduction. Its boundedness supplies a lower bound a and an upper bound b.
Replace a by min(a,b), retaining the upper bound, to get an ordered interval.
The integral finite-level theorem then gives constructibility and Tor amplitude in
this interval for every reduction. Forget the particular interval for finite Tor amplitude.
The reductions are the scalar extensions of the original object; no completion replaces it.
-/
theorem integral_coefficient_hom_reductions
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : D X (integral.{u} ℓ E)) (hK : bc X (integral ℓ E) K) :
    IsDerivedComplete ℓ (ULift.{u} E.val) X K ∧
      ∀ n : ℕ, bc X (finite ℓ E n) ((scalar X (reductionMap ℓ E n)).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalar X (reductionMap ℓ E n)).obj K) := by
  obtain ⟨hc, h₁, _⟩ := IntegralModelsStacks.internal_integral_criterion_forward
    ℓ (ULift.{u} E.val) X K hK
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h₁.1
  have ha' : ((AdicCompletion.derivedReduction ℓ (ULift.{u} E.val) X 0).obj K).IsGE
      (min a b) :=
    DerivedCategory.TStructure.t.isGE_of_ge _ (min a b) a (min_le_left _ _)
  have hbound : ∀ q : ℤ, q < min a b ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction ℓ (ULift.{u} E.val) X 0).obj K)) := by
    intro q hq
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ _).1 ha' q hq
    · exact (DerivedCategory.isLE_iff _ _).1 hb q hq
  obtain ⟨hlevels, _, _⟩ := integral_finite_levels ℓ (ULift.{u} E.val) X K hc h₁
    (min a b) b (min_le_right _ _) hbound
  exact ⟨hc, fun n ↦ ⟨(hlevels n).1, min a b, b, (hlevels n).2⟩⟩

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
