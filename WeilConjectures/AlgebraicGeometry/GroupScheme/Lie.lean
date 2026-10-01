/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The Lie algebra of a group scheme

For a group scheme `G` over a field `k`, the Lie algebra `Lie(G)` is the kernel of the reduction
map `G(k[ε]) → G(k)` on points with values in the dual numbers `k[ε] = k[ε]/(ε²)`: the tangent
vectors at the identity. Here `G(R)` is the group of morphisms `Spec R ⟶ G` over `Spec k`, a group
by Mathlib's `Hom.group`. A homomorphism of group schemes `f : G ⟶ H` induces its differential
`Lie(G) → Lie(H)` by post-composition.

The `k`-module structure and the bracket of `Lie(G)` are not constructed for a general group
scheme; for closed subgroup schemes of `GL_n` they are given concretely in
`WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Lie`.

## Main definitions

- `AlgebraicGeometry.GrpObj.points`: the `R`-points `G(R)` of a group scheme `G` over `k`.
- `AlgebraicGeometry.GrpObj.dualRestrict`: the reduction map `G(k[ε]) →* G(k)`.
- `AlgebraicGeometry.GrpObj.lie`: the Lie algebra `Lie(G) = ker(G(k[ε]) → G(k))`.
- `AlgebraicGeometry.GrpObj.lieMap`: the differential `Lie(G) →* Lie(H)` of a homomorphism.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity,
  via points with values in the dual numbers.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The `R`-points `G(R)` of a group scheme `G` over `k`: the morphisms `Spec R ⟶ G` over
`Spec k`. They form a group by `Hom.group`. -/
abbrev GrpObj.points (R : Type u) [CommRing R] [Algebra k R] :=
  (Spec (.of R)).asOver (Spec (.of k)) ⟶ G

/-- The morphism `Spec k ⟶ Spec k[ε]` over `Spec k` given by `ε ↦ 0`. -/
noncomputable def dualNumberSpecFst :
    (Spec (.of k)).asOver (Spec (.of k)) ⟶ (Spec (.of (DualNumber k))).asOver (Spec (.of k)) :=
  (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).asOver (Spec (.of k))

/-- The reduction map `G(k[ε]) →* G(k)` induced by `ε ↦ 0`. -/
noncomputable def GrpObj.dualRestrict : GrpObj.points G (DualNumber k) →* GrpObj.points G k where
  toFun φ := dualNumberSpecFst ≫ φ
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem GrpObj.dualRestrict_apply (φ : GrpObj.points G (DualNumber k)) :
    GrpObj.dualRestrict G φ = dualNumberSpecFst ≫ φ :=
  rfl

/-- The Lie algebra `Lie(G) = ker(G(k[ε]) → G(k))` of a group scheme `G` over `k`: the points of
`G` with values in the dual numbers that reduce to the identity modulo `ε`.
(blueprint: `sk-d-tangent`) -/
noncomputable def GrpObj.lie : Subgroup (GrpObj.points G (DualNumber k)) :=
  (GrpObj.dualRestrict G).ker

theorem GrpObj.mem_lie {φ : GrpObj.points G (DualNumber k)} :
    φ ∈ GrpObj.lie G ↔ dualNumberSpecFst ≫ φ = 1 :=
  MonoidHom.mem_ker

/-- The group `Lie(G)` is commutative: its group law is the addition of tangent vectors.
(blueprint: `sk-d-tangent`) -/
theorem GrpObj.lie_comm (X Y : GrpObj.lie G) : X * Y = Y * X := by
  sorry

variable {G} {H : Over (Spec (.of k))} [GrpObj H]

theorem GrpObj.comp_mem_lie (f : G ⟶ H) [IsMonHom f] {φ : GrpObj.points G (DualNumber k)}
    (hφ : φ ∈ GrpObj.lie G) : φ ≫ f ∈ GrpObj.lie H := by
  rw [GrpObj.mem_lie] at hφ ⊢
  rw [← Category.assoc, hφ, MonObj.one_comp]

/-- The differential `Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H`, given by
post-composition with `f` on dual-number points. (blueprint: `sk-d-tangent`) -/
noncomputable def GrpObj.lieMap (f : G ⟶ H) [IsMonHom f] : GrpObj.lie G →* GrpObj.lie H :=
  ((IsMonHom.monoidHom f _).comp (GrpObj.lie G).subtype).codRestrict (GrpObj.lie H)
    fun φ ↦ GrpObj.comp_mem_lie f φ.2

@[simp]
theorem GrpObj.coe_lieMap_apply (f : G ⟶ H) [IsMonHom f] (φ : GrpObj.lie G) :
    (GrpObj.lieMap f φ : GrpObj.points H (DualNumber k)) = (φ : GrpObj.points G _) ≫ f :=
  rfl

end AlgebraicGeometry
