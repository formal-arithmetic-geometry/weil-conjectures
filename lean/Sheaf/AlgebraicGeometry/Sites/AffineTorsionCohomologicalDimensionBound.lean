/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.AffineScheme

import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine

/-!
# The affine torsion bound with an explicit upper bound on dimension

Source: blueprint `thm-sc-affine-torsion-cd`.
(blueprint: lem-sc-affine-torsion-cd-explicit-bound)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An explicit dimension bound gives the corresponding bound on derived-section cohomology.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md,
the nonempty affine bound and the separate empty-scheme assertion.
(blueprint: lem-sc-affine-torsion-cd-explicit-bound)

Proof: take the two clauses of the affine theorem. For a nonempty scheme, apply `unbotD`
to the dimension inequality and then `ENat.toNat_le_of_le_natCast`; the resulting natural
dimension is at most `d`. Therefore a degree greater than `d + c` is greater than the
affine theorem's bound. For an empty scheme, its all-degree vanishing clause applies
directly. This also handles dimension zero; no positive-dimension assumption is used.
-/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_isAffine_of_dimension_le
    (K : Type u) [Field K] (c d : ℕ)
    (hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c)
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    HasTorsionEtaleCohomologicalDimensionLE X (d + c) := by
  obtain ⟨hne, hempty⟩ :=
    hasTorsionEtaleCohomologicalDimensionLE_of_isAffine K c hK X
  intro F hF q hq
  rcases isEmpty_or_nonempty X with h | h
  · exact hempty h F hF q
  · have hdim : ((topologicalKrullDim X).unbotD 0).toNat ≤ d := by
      apply ENat.toNat_le_of_le_natCast
      exact (WithBot.unbotD_le_iff (by simp)).2 hX
    exact hne h F hF q (lt_of_le_of_lt (Nat.add_le_add_right hdim c) hq)

end AlgebraicGeometry.Scheme
