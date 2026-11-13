/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affineness from a finite closed cover

## References

* Stacks Project, Limits, Lemma 32.11.3 (Tag 09NL).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme covered set theoretically by finitely many affine closed subschemes is affine.
(Stacks, Tag 09NL) -/
theorem isAffine_of_finite_closed_cover (Y : Scheme.{u}) (r : ℕ)
    (Z : Fin r → Scheme.{u}) (i : ∀ j : Fin r, Z j ⟶ Y)
    [∀ j : Fin r, IsAffine (Z j)] [∀ j : Fin r, IsClosedImmersion (i j)]
    (hcover : ∀ y : Y, ∃ j : Fin r, ∃ z : Z j, i j z = y) : IsAffine Y := by
  let f : (Limits.sigmaObj Z) ⟶ Y := Limits.Sigma.desc i
  have : IsAffine (Limits.sigmaObj Z) := inferInstance
  have : IsFinite f := inferInstance
  have : Surjective f := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨j, z, hz⟩ := hcover y
    exact Set.mem_iUnion.mpr ⟨j, z, hz⟩
  exact isAffine_of_surjective_of_universallyClosed f

end AlgebraicGeometry
