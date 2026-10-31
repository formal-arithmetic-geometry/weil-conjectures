/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RealizationScalarFunctor

/-! # Equivalence for the normalized scalar functor

Source: Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-equivalence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The already constructed scalar functor is fully faithful and essentially surjective.
Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-equivalence)

Proof. Use the integral comparison in s to compute the map on Hom groups by actual
scalar extension. Its cohomology telescope is the uniformizer localization; bounded-below
compactness identifies maps from an integral constructible complex into this telescope
with the localization of integral maps. The fraction normalization of s identifies this
bijection with s.J.map, proving full faithfulness. On a stratum, a finite free continuous
E sheaf admits an integral lattice. The lattice is complete and has the finite quotient
local models required by the integral category. Extend those models by zero across the
stratification. Induct over the finite strata, clearing the finitely many denominators in
each extension arrow by the Hom comparison. This gives integral models for constructible
sheaves. Induct through the bounded truncation triangles for a bounded constructible
complex, again clearing denominators; scalar extension is exact, so its image triangle
identifies the resulting integral complex with the desired one. The module encoding
preserves the underlying sheaves and their local presentations, hence this argument uses
the archived target predicate exactly. The zero complex gives the empty-scheme case.
Thus s.J is full, faithful and essentially surjective, and hence an equivalence. -/
theorem realization_scalar_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) : s.J.IsEquivalence := by
  sorry

end WeilConjectures
