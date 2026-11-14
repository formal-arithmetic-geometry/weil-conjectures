/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Closed subsets are cut out by quasi-coherent ideals

Source: Stacks Project, Schemes, Lemma 26.12.4 (Tag 01J3), construction in its proof.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every closed subset of a scheme is the vanishing locus of a quasi-coherent ideal sheaf.
Quasi-coherent ideal sheaves `𝒥 ⊆ 𝒪_Y` are Mathlib's `Y.IdealSheafData` (compatible affine-local
ideals with `I(D(f)) = I(U)_f`), and the vanishing set `V(𝒥) = {y : 𝒥_y ≠ 𝒪_{Y,y}}` is its
`support`.

Source: Stacks Project, Schemes, Lemma 26.12.4 (Tag 01J3), proof. -/
theorem exists_idealSheafData_support_eq (Y : Scheme.{u}) (Z : Set Y) (hZ : IsClosed Z) :
    ∃ J : Y.IdealSheafData, (J.support : Set Y) = Z := by
  exact ⟨IdealSheafData.vanishingIdeal ⟨Z, hZ⟩,
    IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZ⟩⟩

end AlgebraicGeometry.Scheme
