/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLinePowerComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineDerivedComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineRestrictions
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonIso
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Assembly of signed integral line reduction and restriction

## References

* Stacks Project, Tag 07A4.
* Bhatt--Scholze, *The pro-étale topology for schemes*, Definitions 3.4.10 and 3.5.2,
  Lemma 3.4.12, Proposition 3.5.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem comparison_isIso
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : D.{u, u} l E X none) (hK : IsComplete l E X none K) :
    IsIso ((comparison l E X L m).app K) := by
  have : (power l E X L m).IsFiniteLocallyFreeOfRank 1 := by
    rw [power_eq_coefficient]
    exact (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m).1
  apply integralLineTensorComparison_iso l E X ?_ K hK (power l E X L m)
  intro x
  let := hl x
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
  simpa using (isUnit_of_invertible (l : X.residueField x)).ne_zero

/-- Signed lines commute with all positive derived reductions, preserve derived completeness
and the integral constructible category with each given uniform cohomological interval,
and induce inverse ordinary and completed tensor equivalences on that full category. -/
theorem integral_line_reduction_restriction
    (_hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (_hfinite : FiniteReductions l E X L) :
    ∃ (b : PowerComparisons l E X L) (d : DerivedComparisons l E X L)
      (e : Evaluations l E X L),
      PowerFormula l E X L b ∧ DerivedFormula l E X L b d ∧ EvaluationFormula l E X L e ∧
      (∀ (m : ℤ) (K : D.{u, u} l E X none), IsComplete l E X none K →
        IsIso ((comparison l E X L m).app K) ∧
          IsComplete l E X none ((ordinary l E X L m).obj K)) ∧
      (∀ (m : ℤ) (K : D.{u, u} l E X none) (a z : ℤ),
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a z) →
        ∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((ordinary l E X L m).obj K)) ⊆ Set.Icc a z) ∧
      Restrictions l E X L e := by
  obtain ⟨b, e, hb, he⟩ := integral_line_power_comparisons l E X L
  obtain ⟨d, hd, hs⟩ := integral_line_derived_comparisons l E X L b hb
  obtain ⟨hc, hr⟩ := integral_line_restrictions l E X _hl L _hfinite e he
  refine ⟨b, d, e, hb, hd, he, ?_, hs, hr⟩
  intro m K hK
  exact ⟨comparison_isIso l E X _hl L m K hK, hc m K hK⟩

end WeilConjectures.IntegralLineReduction
