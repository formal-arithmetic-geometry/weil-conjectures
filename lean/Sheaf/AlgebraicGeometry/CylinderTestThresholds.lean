/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CommonMarkedTestSequence
public import Sheaf.AlgebraicGeometry.RestrictedMarkedTests
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift

/-! # Common cylinder divisor tests

Source: Bierstone--Milman, Theorem 6.1, pp. 631--632, and steps 1--6 and 11
of the numerical recovery plan (blueprint: lem-trf-cylinder-test-thresholds).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Equivalent marked tests give the same answers to cylinder divisor tests.
Source: BM, Theorem 6.1, pp. 631--632; agent geometric refinement of the cylinder
argument (blueprint: lem-trf-cylinder-test-thresholds).

Proof: A common finite prefix leaves the same suffix tests, by induction on its
geometric and open-restriction constructors. Smoothness, finite type, adapted boundary
coordinates, and equal local support dimensions persist along that prefix: coordinate
charts handle blowups and line products; the dimension formula identifies local dimensions
from the common residue field and equal dimensions of the surviving components.
At the given common cosupport point, shrink to the common smooth reduced closure and use
normal completions over its residue field. Their number of normal variables is equal.
Adjoin a line with parameter t and its zero section. After k section blowups the controlled
ideal has the formula t^(-kd) K(t^k u). The isotropic calculation shows that these section
centers stay in cosupport, including zero ideals and zero normal dimension. Shrink for each
finite tower to spread the containment from the generic section point to its smooth center.
A divisor test asks whether the newest exceptional divisor meets cosupport in a germ of full
local dimension. A proper closed germ in its regular local domain has smaller dimension,
so the answer is read from the common cosupport and common local dimension. A positive
answer is precisely divisibility by t^d; the controlled chart theorem permits the common
divisor-center blowup and divides the ideal by t^d. Repeat only after successful tests.
After i divisions the next test succeeds precisely when k(m-d) >= (i+1)d for finite m,
and always for the zero ideal. Rewrite this as (k+i+1)d <= km. Thus the two data have the
same displayed inequalities for all positive k and natural i. No numerical supremum or
point-order equality is used in constructing these common tests. -/
theorem cylinder_test_thresholds
    (S : Embedded (ULift.{u} ℚ)) (M P : Marked S)
    [LocallyOfFiniteType S.p] [QuasiCompact S.p]
    (hboundary : IsStrictNormalCrossingsBoundary
      (⨅ i : Fin S.boundary.length, S.boundary.get i))
    (hordered : HasAdaptedNormalCrossingsCenter (⊥ : S.Z.IdealSheafData)
      (fun i ↦ S.boundary.get i))
    (hM : HasAdaptedNormalCrossingsCenter (⊥ : M.N.IdealSheafData)
      (fun i ↦ (S.boundary.get i).comap M.j))
    (hP : HasAdaptedNormalCrossingsCenter (⊥ : P.N.IdealSheafData)
      (fun i ↦ (S.boundary.get i).comap P.j))
    (hdim : ∀ (x : M.N) (y : P.N), M.j x = P.j y →
      ringKrullDim (M.N.presheaf.stalk x) = ringKrullDim (P.N.presheaf.stalk y))
    (hequivalent : RestrictedEquivalent M P) :
    ∀ (T : Embedded (ULift.{u} ℚ)) (M' P' : Marked T),
      CommonTestSequence M P M' P' →
      ∀ (x : M'.N) (y : P'.N), M'.j x = P'.j y →
        M'.j x ∈ M'.cosupport → P'.j y ∈ P'.cosupport →
        ∀ (k : ℕ), 0 < k → ∀ i : ℕ,
          (((k + i + 1) * M'.marking : ℕ) : ℕ∞) ≤ (k : ℕ∞) * order M'.ideal x ↔
          (((k + i + 1) * P'.marking : ℕ) : ℕ∞) ≤ (k : ℕ∞) * order P'.ideal y := by
  sorry

end AlgebraicGeometry.HilbertSamuel
