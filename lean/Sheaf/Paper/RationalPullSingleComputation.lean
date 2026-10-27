/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.RationalStratumPullbackData


/-! # Computation of rational derived pullback on single sheaves -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RationalStratumPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A normalized pullback computes a single if scalars are unchanged or the sheaf is
finite locally free. Source: Stacks 06YY; Bhatt--Scholze Definitions 6.8.3/6.8.6
(blueprint: lem-per-rational-pull-single-computation).

Proof: if the coefficient map is invertible, its scalar extension is exact, as is
module inverse image. Their derived functor is their termwise functor, and its
canonical counit is invertible on every complex. The normalization of p identifies
its counit with this counit, so the single comparison is invertible. Otherwise,
trivialize the finite locally free sheaf on a covering. Tensoring its degree-zero
complex is locally a finite direct sum of the identity on complexes. This preserves
acyclicity, including the empty sum. Exact restriction commutes with cohomology,
and sheaf separatedness detects vanishing on the cover, so this single is K-flat.
Apply p.computes. The remaining map is the canonical termwise single isomorphism,
which is invertible. No flatness of the structural coefficient map is required. -/
theorem rational_pull_single_computation {X Y : Scheme.{u}} (f : Y ⟶ X)
    {c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E} (p : Pull l E f c)
    (M : pbcModules X (rationalCoefficientSheaf l X E))
    (hM : IsIso c ∨ M.IsFiniteLocallyFree) : IsIso (p.singleMap l E M) := by sorry

end AlgebraicGeometry.Scheme.RationalStratumPullback
