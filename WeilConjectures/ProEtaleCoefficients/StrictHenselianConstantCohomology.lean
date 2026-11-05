/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-!
# Constant-sheaf cohomology over a strictly henselian local scheme

Source: Stacks Project, Tag 03QO and Tag 03P5; blueprint statement
`sbc-lem-strict-henselian-constant-cohomology`.
-/

universe u

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
-- The hypothesis `hA` belongs to the blueprint statement but is not needed in the proof.
/-- For a strictly henselian local ring, finite constant étale cohomology is concentrated
in degree zero, where it is canonically the coefficient group.

The degree-zero equivalence is `Scheme.hZeroConstantSheafAddEquiv`; positive-degree
vanishing is expressed by `Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing`.
The assumptions `[Finite A]` and `IsUnit (Nat.card A : R)` encode that the constant
coefficient group is finite and has order invertible in `R`.

Proof steps recorded by the source: (1) finite etale covers split and an etale
neighbourhood of the closed point has a section (Stacks Tag 03QO); (2) these sections
make global sections exact; (3) apply the exact-functor calculation to a K-injective
resolution in the definition of etale cohomology; (4) `Spec R` is connected and the
constant-section map identifies degree zero with `A` (Stacks Tag 03P5).

Source: Stacks Project, Tags 03QO and 03P5
(blueprint: sbc-lem-strict-henselian-constant-cohomology). -/
theorem strictHenselian_constant_cohomology
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    (A : AddCommGrpCat.{u + 1}) [Finite A] (hA : IsUnit (Nat.card A : R)) :
    Nonempty (Sheaf.H ((constantSheaf (Spec (.of R)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj A) 0 ≃+ A) ∧
      ∀ q : ℕ, 0 < q → Subsingleton
        (Sheaf.H ((constantSheaf (Spec (.of R)).smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj A) q) := by
  refine ⟨⟨Scheme.hZeroConstantSheafAddEquiv R A⟩, ?_⟩
  intro q hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simpa [Nat.succ_eq_add_one] using
    (Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing (R := R)
      ((constantSheaf (Spec (.of R)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj A) n)
