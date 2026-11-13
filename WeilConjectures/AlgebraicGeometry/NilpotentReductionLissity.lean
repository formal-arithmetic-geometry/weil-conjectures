/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientScalarEquivalence
import WeilConjectures.AlgebraicGeometry.NilpotentReductionStep

/-! # Lissity propagates through powers of a coefficient ideal

## References

* Stacks Project, Cohomology on Sites, Tags 094I and 094H.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Lissity of all cohomology sheaves after reduction modulo an ideal implies lissity
modulo every positive power, and implies lissity of the original object for a nilpotent
ideal (Stacks, Tags 094I and 094H). -/
theorem locallyConstantFiniteTypeModules_reduction_pow
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K))) :
    (∀ m : ℕ, 1 ≤ m →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ m)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((constantCoefficientScalarExtension T.toGrothendieck
            (Ideal.Quotient.mk (J ^ m))).obj K))) ∧
    (∀ m : ℕ, 1 ≤ m → J ^ m = ⊥ →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck B
        ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  let lisseReduction (I : Ideal B) : Prop :=
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk I)).obj K))
  have hpow (m : ℕ) (hm : 1 ≤ m) : lisseReduction (J ^ m) := by
    induction m, hm using Nat.le_induction with
    | base =>
        rw [pow_one]
        exact hmod
    | succ n hn ih =>
        exact locallyConstantFiniteTypeModules_reduction_succ T B J K hbounded hmod n hn ih
  refine ⟨hpow, ?_⟩
  intro m hm hzero i
  apply locallyConstantFiniteTypeModules_of_scalarExtension_bijective
    T.toGrothendieck (Ideal.Quotient.mk (J ^ m)) ?_ K i (hpow m hm i)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hmem : x - y ∈ J ^ m := (Ideal.Quotient.eq_zero_iff_mem).mp (by
      simpa only [map_sub, sub_eq_zero] using hxy)
    simpa only [hzero, Ideal.mem_bot] using hmem
  · exact Ideal.Quotient.mk_surjective

end SheafOfModules
