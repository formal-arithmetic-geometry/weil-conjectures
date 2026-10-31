/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The two signed-twist membership clauses split from the first formula theorem.
(blueprint: lem-fd-fourier-twist-membership-split) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedFintypeInType false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The two signed-twist membership clauses in the first Fourier formula.

Source: current blueprint, lem-fd-first-formula.proof.md, the six membership clauses (the
twisted-skyscraper memberships), with the Tate lines of sk-def-sp-tate-twist
(blueprint: lem-fd-fourier-twist-membership-split).

Proof in words. The characteristic of k is p, different from ell, so on the affine line over
k the positive Tate line of either coefficient model (the rational line for E, its
sheafified colimit over finite subextensions for the algebraic closure) is locally free of
rank one; hence so is its dual, the signed power -1. The origin skyscraper is bounded
constructible (closed direct image of the regular complex). Derived tensor of a bounded
constructible complex with a locally free module in degree zero is bounded constructible,
and the shift by -1 preserves bounded constructibility. -/
theorem first_formula_twist_membership_split
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  boundedConstructible _ ((shiftFunctor _ (-1 : ℤ)).obj
    (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _
      (spRationalTwist (AffineSpace PUnit (Spec (.of k))) ℓ E)
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
        (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
            (Spec (.of k)))))) (-1))) ∧
  boundedConstructible _ ((shiftFunctor _ (-1 : ℤ)).obj
    (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _
      (spQbarTwist (AffineSpace PUnit (Spec (.of k))) ℓ)
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (Spec (.of k)))))) (-1))) := by
  sorry

end AlgebraicGeometry.ProEtale
