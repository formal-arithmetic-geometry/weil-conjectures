/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Normal integral components of a Noetherian etale scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, node
`lem-fin-etale-normal-components`, order 1605; Stacks Project, Tag 033C
(blueprint: lem-fin-etale-normal-components).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An etale morphism with Noetherian source and normal integral target has a finite
partition into clopen normal integral open subschemes. Normality uses the convention of
`def-sbc-normal-dominant-galois`, so it includes integrality.

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1605; Stacks Project, Tag 033C
(blueprint: lem-fin-etale-normal-components).

Proof: Choose affine neighborhoods of a source point and its image. Their ring map is etale
by `def-weil-pbc-scheme-conventions`. Normality of the target makes the target affine ring
normal. By `lem-weil-pbc-etale-over-normal-ring-normal` the source affine ring is normal,
so every source stalk is a normal domain and the source is reduced. By
`lem-weil-pbc-noetherian-finite-components`, the Noetherian source has finitely many
irreducible components. Distinct components cannot meet: an intersection point would have
more than one minimal prime in its local ring, contradicting that it is a domain.
Each component is closed, and its complement is the finite union of the other closed
components, hence it is also open. The components cover the source. On each component the
stalks are the source stalks, hence normal domains; reducedness and irreducibility make it
integral as in `def-sbc-normal-dominant-galois`. Enumerate these components by `Fin n`.
The empty source is covered by the empty family (`n = 0`). -/
theorem Etale.exists_clopen_normal_integral_components
    {W Y : Scheme.{u}} (f : W ⟶ Y) [Etale f] [IsNoetherian W]
    (hY : IsNormalScheme Y) :
    ∃ (n : ℕ) (U : Fin n → W.Opens),
      (∀ i, IsClosed (U i : Set W)) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧
      (∀ i, IsNormalScheme (U i).toScheme) := by
  sorry

end AlgebraicGeometry
