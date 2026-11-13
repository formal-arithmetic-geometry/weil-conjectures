/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.Curve.ExistsAmpleOfDimLEOne

/-!
# Quasi-projectivity in dimension at most one

Source: Stacks Project, Varieties, Lemma 0A25.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite-type scheme over a field of dimension at most one admits a closed
immersion into an open subscheme of a finite-dimensional projective space over that field.
Here `ℙᴺ_k = Proj(k[x₀, …, x_N])` is `ℙ(ULift (Fin (N + 1)); Spec k)`, the projective space
of `def-pc-projective-morphism` (`IsHProjective`).
Source: Stacks Project, Varieties, Lemma 0A25. -/
theorem exists_closed_open_immersion_projectiveSpace_of_dim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (hdim : X.dim ≤ 1) :
    ∃ (N : ℕ) (U : Scheme.{u}) (g : U ⟶ Spec (.of k))
      (i : X ⟶ U) (j : U ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))),
      IsClosedImmersion i ∧ IsOpenImmersion j ∧ i ≫ g = f ∧
        j ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k) = g := by
  obtain ⟨L, hL, hample⟩ := Scheme.Modules.exists_isAmple_of_dim_le_one f
    (by simpa only [← X.dim_eq_topologicalKrullDim] using hdim)
  let := hL
  obtain ⟨d, hd, N, e, he, hef, _⟩ :=
    hample.exists_immersion_affine_base k X f L
  obtain ⟨U, i, j, hi, hj, hij⟩ := IsImmersion.isImmersion_iff_exists.mp he
  refine ⟨N, U, j ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k),
    i, j, hi, hj, ?_, rfl⟩
  rw [← Category.assoc, hij, hef]

end AlgebraicGeometry
