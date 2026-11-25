/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.PopescuWeakClearCore
import WeilConjectures.RingTheory.PopescuWeakClearRelations

/-!
# Clearing a local standard smooth presentation

We clear the coefficients and ideal-membership certificates of a submersive presentation over
`R_p`, obtaining equations `f_j` over `R` with `s₀ - h * det ∈ (f)` and `s_(j+1) * g_j ∈ (f)`
for scalars outside `p`.

## Implementation details

This concerns only the base localization and its polynomial presentation; neither a global
factorization nor a singular ideal is constructed. Empty families use the empty determinant and
empty products `1`.

## References

* [Stacks, Tag 07F9] (the denominator-clearing paragraphs of the proof)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Clear the coefficients and ideal-membership certificates of a submersive
presentation over `Rₚ`. -/
theorem exists_cleared_submersive_presentation
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {D : Type v} [CommRing D] [Algebra (Localization.AtPrime p) D]
    [Algebra R D] [IsScalarTower R (Localization.AtPrime p) D]
    (n m c t : ℕ) (hc : c ≤ n + m)
    (P : SubmersivePresentation (Localization.AtPrime p) D (Fin (n + m)) (Fin c))
    (hmap : P.map = Fin.castLE hc)
    (g : Fin t → MvPolynomial (Fin n) R)
    (hg : ∀ j, aeval (fun i : Fin n ↦ P.val (Fin.castAdd m i)) (g j) = 0) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (s : Fin (t + 1) → R) (h : MvPolynomial (Fin (n + m)) R),
      (∀ j, s j ∉ p) ∧
      (MvPolynomial.C (s 0) - h * Matrix.det
        (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) ∈
          Ideal.span (Set.range f)) ∧
      (∀ j : Fin t, MvPolynomial.C (s j.succ) *
        rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈ Ideal.span (Set.range f)) ∧
      (∀ j, aeval P.val (f j) = 0) := by
  classical
  obtain ⟨f, s0, h, hs0, hdet, hf, hkernel⟩ :=
    exists_cleared_submersive_presentation_core p n m c hc P hmap
  obtain ⟨sr, hsr, hgr⟩ :=
    exists_cleared_submersive_relations p n m c t P f hkernel g hg
  let s : Fin (t + 1) → R := Fin.cases s0 (fun j ↦ sr j)
  refine ⟨f, s, h, ?_, hdet, ?_, hf⟩
  · intro j
    exact Fin.cases hs0 (fun j ↦ hsr j) j
  · intro j
    exact hgr j

end Algebra
