/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Generator substitution for Koszul complexes

Source: Stacks Project, Tags 0BQY and 0BQZ.
(blueprint: new-q2-koszul-generator-chain-map).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The Koszul boundary on a wedge is the alternating contraction sum.
Source: Stacks Project, Tags 0BQY and 0BQZ; the contraction formula in
`koszul_differential`. Shared by generator substitution and top evaluation.
(blueprint: new-q2-koszul-generator-chain-map).

Proof: Uniqueness in koszul_differential identifies its derivation with
contractLeft at the zero quadratic form, since both kill one and obey the same
recursion on a generator times an exterior-algebra element. Apply the resulting
wedge formula and compare the underlying exterior-algebra elements by
Subtype.ext; scalar multiplication gives the displayed contraction sum. -/
theorem boundary_wedge
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (n : ℕ) (v : Fin (n + 1) → (Fin r →₀ A)) :
    koszulBoundary A r f n (exteriorPower.ιMulti A (n + 1) v) =
      ∑ i : Fin (n + 1),
        (((-1 : A) ^ (i.val + 2)) * Finsupp.linearCombination A f (v i)) •
          exteriorPower.ιMulti A n (v ∘ i.succAbove) := by
  classical
  let l := Finsupp.linearCombination A f
  obtain ⟨D, hD1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hdu⟩ :=
    koszul_differential A (Fin r →₀ A) l
  have hc : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A))) l = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin r →₀ A))) l v y
  apply Subtype.ext
  change CliffordAlgebra.contractLeft _ _ = _
  rw [hc]
  change D (ExteriorAlgebra.ιMulti A (n + 1) v) = _
  rw [hform]
  simp [l, Algebra.smul_def]


end ExteriorAlgebra
