/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# The coordinate algebra of an affine finite-type scheme over a field

Source: Stacks Project, Morphisms, Lemma 29.15.2 (Tag 01T2), (1) implies (2)
(blueprint: lem-pc-affine-finite-type-algebra).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-affine-finite-type-algebra) Let `Y` be an affine scheme of finite type
over a field `k`. Its global sections, with the algebra structure induced by the structure
morphism and `Γ(Spec k) ≅ k`, form a finite-type `k`-algebra (Stacks, Tag 01T2).

Proof: the finite-type morphism is locally of finite type. Apply the affine-pair
characterization of locally finite type to `U = Y` and `V = Spec k`. Their global-section
ring map is of finite type, and `Γ(Spec k) ≅ k` identifies this with finite generation of
`Γ(Y, ⊤)` as a `k`-algebra. -/
theorem affine_finiteType_algebra_of_field {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsAffine Y] (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    (letI := ((f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
     Algebra.FiniteType k Γ(Y, ⊤)) := by
  sorry

end AlgebraicGeometry
