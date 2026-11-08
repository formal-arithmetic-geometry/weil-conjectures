/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Submission.WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Qcqs higher direct images preserve a fixed set of torsion primes

Source: Stacks Project, Tags 0DDD (1) and 0DDC (1), fixed-prime refinement
(blueprint: lem-sbc-qcqs-higher-images-prime-torsion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The small divisibility index for the restricted kernel union in Stacks Tag 0DDC.
The integer 1 is allowed even when P has no prime members. -/
private structure PrimeAnnihilator (P : Set ℕ) where
  val : ℕ
  pos : 0 < val
  allowed : ∀ p : ℕ, p.Prime → p ∣ val → p ∈ P

private instance (P : Set ℕ) : PartialOrder (PrimeAnnihilator P) where
  le n m := n.val ∣ m.val
  lt n m := n.val ∣ m.val ∧ ¬m.val ∣ n.val
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl n := dvd_refl n.val
  le_trans _ _ _ := dvd_trans
  le_antisymm n m hnm hmn := by
    cases n
    cases m
    congr
    exact Nat.dvd_antisymm hnm hmn

end AlgebraicGeometry.Etale
