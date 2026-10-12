/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Finite basic-open covers generate the unit ideal under ideal H¹ vanishing

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs of the proof (blueprint: lem-pqf-h1-finite-basic-cover-unit-ideal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Ideal H¹ vanishing makes any finite basic-open covering family generate one.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs of the proof (blueprint: lem-pqf-h1-finite-basic-cover-unit-ideal).

Proof: Enumerate the finite set s by f₁,...,fₙ. The map O_X^n → O_X sending
eᵢ to fᵢ is surjective on stalks, since at every point one fᵢ is a unit.
Let F be its quasi-coherent kernel. Put Fᵢ = F ∩ O_X^i, using the first i
summands. Projection onto the i-th coordinate identifies Fᵢ/Fᵢ₋₁ with a
quasi-coherent ideal subsheaf of O_X. Begin with F₀ = 0. The exact segment
H¹(Fᵢ₋₁) → H¹(Fᵢ) → H¹(Fᵢ/Fᵢ₋₁), with both outer terms zero, proves
H¹(Fᵢ) = 0 by induction, hence H¹(F) = 0. The initial long exact segment
for 0 → F → O_X^n → O_X → 0 makes the map on global sections surjective.
A preimage of 1 gives coefficients aᵢ with sum aᵢ fᵢ = 1. Therefore
1 belongs to Ideal.span s and that ideal is the whole ring.
For the empty covering family, X is empty and its section ring is the zero
ring; the same conclusion holds. The basic opens need not be affine. -/
theorem span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    (s : Set Γ(X, ⊤)) (hs : s.Finite)
    (hcover : ∀ x : X, ∃ f ∈ s, x ∈ X.basicOpen f) :
    Ideal.span s = ⊤ := by sorry

end AlgebraicGeometry
