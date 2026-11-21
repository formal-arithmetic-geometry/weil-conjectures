/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique

/-!
# The ring of integers of a finite extension of the p-adic numbers

Source: Serre, Local Fields, Chapter II, §2, Proposition 3 and Chapter I, §1, Proposition 1.
-/

@[expose] public section

universe u

namespace Padic

/-- The sets of elements of absolute value at most one and less than one in a finite
extension of `ℚ_[l]` form its ring of integers and maximal ideal. The ring is a DVR with
finite residue field. Uniformizers attain the largest nonzero value in the maximal ideal,
exist, and differ by units; every nonzero field element has a unique unit-times-integer-power
expression for a fixed uniformizer.

Source: Serre, Local Fields, Chapter II, §2, Proposition 3 and Chapter I, §1, Proposition 1. -/
theorem extension_integers_dvr (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (abv : AbsoluteValue E ℝ)
    (h_ext : ∀ a : ℚ_[l], abv (algebraMap ℚ_[l] E a) = ‖a‖) :
    ∃ O : Subring E, ∃ m : Ideal O,
      (∀ x : E, x ∈ O ↔ abv x ≤ 1) ∧
      (∀ x : O, x ∈ m ↔ abv (x : E) < 1) ∧
      (∀ x : O, IsUnit x ↔ abv (x : E) = 1) ∧
      IsLocalRing O ∧ m.IsMaximal ∧
      (∀ J : Ideal O, J.IsMaximal → J = m) ∧
      IsFractionRing O E ∧
      IsDiscreteValuationRing O ∧ IsPrincipalIdealRing O ∧ m ≠ ⊥ ∧
      (∀ J : Ideal O, J.IsPrime ∧ J ≠ ⊥ ↔ J = m) ∧
      Finite (O ⧸ m) ∧
      (∃ r : ℝ,
        (∃ y : O, y ∈ m ∧ y ≠ 0 ∧ abv (y : E) = r) ∧
        (∀ y : O, y ∈ m → y ≠ 0 → abv (y : E) ≤ r) ∧
        (∀ π : O, Ideal.span ({π} : Set O) = m ↔ π ≠ 0 ∧ abv (π : E) = r)) ∧
      (∃ π : O, Ideal.span ({π} : Set O) = m) ∧
      (∀ π π' : O, Ideal.span ({π} : Set O) = m →
        Ideal.span ({π'} : Set O) = m → ∃ v : Oˣ, π' = (v : O) * π) ∧
      (∀ π : O, Ideal.span ({π} : Set O) = m → ∀ x : Eˣ,
        ∃! p : Oˣ × ℤ, (x : E) = ((p.1 : O) : E) * (π : E) ^ p.2) := by
  obtain ⟨O, m, hcore⟩ := extension_integers_dvr_core l E abv h_ext
  rcases hcore with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr,
    hpid, hm0, hprime, hfinite, hr, hgen⟩
  obtain ⟨hassoc, hexists⟩ :=
    extension_integers_dvr_factorization E O m hdvr hm0 hmax hfrac hgen
  have hunique := extension_integers_dvr_factorization_unique E O m hdvr hmax hfrac
  refine ⟨O, m, hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen, hassoc, ?_⟩
  intro π hπ x
  obtain ⟨p, hp⟩ := hexists π hπ x
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (hunique π hπ x p q hp hq).symm

end Padic
