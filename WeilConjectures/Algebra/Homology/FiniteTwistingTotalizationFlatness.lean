/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-! # K-flatness of finite twisting totalizations

This helper isolates the bounded-above flatness argument once a realization record
has been supplied.
-/

/- The flatness criterion is an existing dependency of the finite totalization construction. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

/-- If the terms of every graded complex are flat, the finite direct-sum totalization
and all of its tail complexes are K-flat. Choose a common upper bound for the
bounded graded complexes, use finite biproduct flatness for every totalization term
and tail term, and apply the bounded-above-flat K-flat criterion (Stacks, Tag 06YQ).
The assumed K-flatness of the graded complexes is retained in the interface but is
not needed by this bounded-above argument.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (step 3 of lem-trf-filtered-mapping-cylinder-step).
(blueprint: lem-trf-finite-filtered-totalization-flatness) -/
theorem finiteTwistingTotalization_kflat_of_flat
    (a b : ℤ) (hab : a ≤ b) (D : FiniteTwistingFamily R a b)
    (M : FiniteTwistingTotalization D)
    (hflat : (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
      SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc a b), (D.G p).IsKFlatIndependentCoefficients)) :
    M.P.IsKFlatIndependentCoefficients ∧
      ∀ r : ℤ, IsKFlatIndependentCoefficients (J := J) (R := R)
        (M.F.step r : CochainComplex (ringedSiteModules.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) := by
  sorry

end CochainComplex
