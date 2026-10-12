/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps

/-! # Columnwise comparison of cutoff quotients and smart windows

Source: the columnwise smart truncation argument in Stacks Project, Homology, Tag 012X.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The quotient of nested cutoffs has a columnwise quasi-isomorphism to the window.
Source: Stacks Project, Homology, Tag 012X, smart truncation filtration construction;
Mathlib's complementary smart truncations.
(blueprint: lem-sp-vertical-cutoff-quotient-comparison)

Proof: each column inclusion is the unique map between the smart cutoffs compatible
with their inclusions into the original column. Compose the b-cutoff with the smart
projection in degrees >= a and truncate above b-1. This annihilates the a-cutoff,
so factors through its cokernel. These projections are natural in the column, and
therefore give a bicomplex morphism from the cokernel to the smart window. For a < b,
the quotient in degree a-1 is the image of the original differential from a-1 to a.
The map to the window is zero there, the quotient projection in degree a, and an
isomorphism in higher degrees. Its kernel is the two-term complex with this image
in degrees a-1 and a and identity differential; it is acyclic. At b=a+1 the target
in degree a is cycles modulo boundaries, with the same acyclic kernel. If a=b,
both quotient and window are zero. Negative degrees of the original extended column
are zero: when a=0 the image in degree -1 is zero, so restriction to the naturals
preserves the comparison; when a<0 it is already an isomorphism. Hence every column
map is a quasi-isomorphism, including all negative-endpoint cases. -/
theorem verticalCutoff_cokernel_column_comparison
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (a b : ℤ) (hab : a ≤ b)
    (f : (((verticalCutoff a).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ⟶
      (((verticalCutoff b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    (hf : f ≫ ((verticalCutoffι b).mapHomologicalComplex (ComplexShape.up ℕ)).app K =
      ((verticalCutoffι a).mapHomologicalComplex (ComplexShape.up ℕ)).app K) :
    ∃ q : cokernel f ⟶
      (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K),
      ∀ p : ℕ, QuasiIso (q.f p) := by
  sorry

end HomologicalComplex₂
