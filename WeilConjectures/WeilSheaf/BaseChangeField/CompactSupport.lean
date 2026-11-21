/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

/-!
# Compactly supported cohomology under a finite extension of the base field

Let `k₀ ⊆ K` be finite fields with `[K : k₀] = m` and `X` a separated `k₀`-scheme of finite
type. A finite extension of the constant field does not change the geometric scheme
`X ⊗_{k₀} k̄`, nor a Weil sheaf on it, nor its cohomology; it replaces the geometric Frobenius of
`k₀` by its `m`-th power. So a Weil sheaf `F` on `X` gives a Weil sheaf `F_K` on
`X_K = X ×_{k₀} K`, lisse if `F` is and punctually pure of the same weight, with
`H_c^r(X_K ⊗_K k̄, F_K) = H_c^r(X ⊗_{k₀} k̄, F)` and the Frobenius of `K` acting as `Fᵐ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_compactlySupportedCohomology_baseChangeField`.

## Implementation details

The instances `IsSeparated` and `QuasiCompact` for the structure morphism of `X_K` are stated
here rather than next to `AlgebraicGeometry.Scheme.baseChangeField`, to keep that widely imported
file light.

The comparison of `Rf_!` with the transport of Weil sheaves along the identification of geometric
fibres (`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) is not available yet: the analogue for
the ordinary direct image is
`AlgebraicGeometry.ProEtaleWeilSheaf.transportRightDerivedLowerStarIso`, while `Rf_!` depends on
a choice of compactification.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  (K : Type u) [Field K] [Algebra k₀ K]

instance [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    IsSeparated (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback _ _) ‹_›

instance [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    QuasiCompact (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback _ _) ‹_›

namespace WeilSheaf

variable [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X}
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [Finite K] [Fact (ringChar K ≠ l)]

/-- **Weil sheaves under a finite extension of the base field.** Let `K` be a finite extension
of `k₀` of degree `m` and `F` a Weil sheaf on a separated `k₀`-scheme `X` of finite type. There
is a Weil sheaf `F_K` on `X_K = X ×_{k₀} K`, the restriction of `F`, which is lisse if `F` is
lisse and punctually `ι`-pure of weight `w` if `F` is, and whose compactly supported cohomology
`H_c^r(X_K ⊗_K k̄, F_K)` is `H_c^r(X ⊗_{k₀} k̄, F)` with the geometric Frobenius of `K` acting
as the `m`-th power of that of `k₀`. -/
theorem exists_compactlySupportedCohomology_baseChangeField (F : WeilSheaf k₀ l X) :
    ∃ F' : WeilSheaf K l (X.baseChangeField k₀ K),
      (F.IsLisse → F'.IsLisse) ∧
      (∀ (ι : PadicAlgCl l →+* ℂ) (w : ℝ), F.IsPunctuallyPureOfWeight ι w →
        F'.IsPunctuallyPureOfWeight ι w) ∧
      ∀ r : ℤ, Nonempty ((F'.compactlySupportedCohomology r).Equiv
        ((F.compactlySupportedCohomology r).powFrobenius (Module.finrank k₀ K))) := by
  sorry

end WeilSheaf

end AlgebraicGeometry
