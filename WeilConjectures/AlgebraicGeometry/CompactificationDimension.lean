/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Compactifications of the same dimension

An affine scheme of finite type over a field is a quasi-compact open subscheme of a proper
scheme of the same dimension: the scheme-theoretic closure of it in a Nagata compactification.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Compactification without raising the dimension.** An affine scheme `X` of finite type
over a field `k` with `dim X ≤ d` is a quasi-compact open subscheme of a proper `k`-scheme `Y`
with `dim Y ≤ d` (the scheme-theoretic closure of `X` in a Nagata compactification). -/
theorem exists_isProper_isOpenImmersion_topologicalKrullDim_le {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (b : Y ⟶ Spec (.of k)) (j : X ⟶ Y), IsProper b ∧ IsOpenImmersion j ∧
      QuasiCompact j ∧ j ≫ b = a ∧ topologicalKrullDim Y ≤ (d : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry
