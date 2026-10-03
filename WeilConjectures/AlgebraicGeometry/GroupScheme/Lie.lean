/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The tangent group of a group scheme

For a group scheme `G` over a commutative ring `k`, the tangent space `T_1 G` at the identity is
the kernel of the reduction map `G(k[ε]) → G(k)` on points with values in the dual numbers
`k[ε] = k[ε]/(ε²)`. Here `G(R)` is the group of morphisms `Spec R ⟶ G` over `Spec k`, a group by
Mathlib's `Hom.group`, and `R ↦ G(R)` is functorial in `k`-algebra homomorphisms. A homomorphism
of group schemes `f : G ⟶ H` induces its differential `T_1 G → T_1 H` by post-composition.

Only the underlying abelian group of `T_1 G` is constructed here: the `k`-module structure (from
the scalings `ε ↦ cε` of `k[ε]`) and the Lie bracket of the Lie algebra `Lie(G)` are not. For
closed subgroup schemes of `GL_n` the Lie algebra is given concretely in
`WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Lie`, and identified with the
tangent group there.

## Main definitions

- `AlgebraicGeometry.points`: the `R`-points `G(R)` of a scheme `G` over `k`.
- `AlgebraicGeometry.pointsMap`: the group homomorphism `G(R) →* G(S)` induced by `R →ₐ[k] S`.
- `AlgebraicGeometry.tangentGroup`: the tangent group `T_1 G = ker(G(k[ε]) → G(k))`.
- `AlgebraicGeometry.tangentGroupMap`: the differential `T_1 G →* T_1 H` of a homomorphism.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity,
  via points with values in the dual numbers.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [CommRing k] (G : Over (Spec (.of k)))

/-- The `R`-points `G(R)` of a scheme `G` over `k`: the morphisms `Spec R ⟶ G` over `Spec k`. For a
group scheme `G` they form a group by `Hom.group`. -/
abbrev points (R : Type u) [CommRing R] [Algebra k R] :=
  (Spec (.of R)).asOver (Spec (.of k)) ⟶ G

variable [GrpObj G] {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- The group homomorphism `G(R) →* G(S)` induced by a `k`-algebra homomorphism `φ : R → S`:
precomposition with `Spec φ : Spec S ⟶ Spec R`. -/
noncomputable def pointsMap (φ : R →ₐ[k] S) : points G R →* points G S where
  toFun x := (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

@[simp]
theorem pointsMap_apply (φ : R →ₐ[k] S) (x : points G R) :
    pointsMap G φ x = (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫ x :=
  rfl

/-- The tangent group `T_1 G = ker(G(k[ε]) → G(k))` of a group scheme `G` over `k`: the points of
`G` with values in the dual numbers that reduce to the identity modulo `ε`. It is the underlying
group of the Lie algebra of `G`; its `k`-module structure and bracket are not constructed here.
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentGroup : Subgroup (points G (DualNumber k)) :=
  (pointsMap G (TrivSqZeroExt.fstHom k k k)).ker

theorem mem_tangentGroup {x : points G (DualNumber k)} :
    x ∈ tangentGroup G ↔ pointsMap G (TrivSqZeroExt.fstHom k k k) x = 1 :=
  MonoidHom.mem_ker

/-- The tangent group is commutative: its group law is the addition of tangent vectors.

Proof sketch (not formalised): over `S = k[ε₁, ε₂]/(ε₁, ε₂)²`, the two maps `k[ε] → S` given by
`ε ↦ ε₁` and `ε ↦ ε₂` exhibit `S` as the fibre product `k[ε] ×_k k[ε]`. Since `G` is
representable, `G(S) = G(k[ε]) ×_{G(k)} G(k[ε])`, and both products `XY` and `YX` of two tangent
vectors are the image of the same point of `G(S)` under the multiplication `ε₁, ε₂ ↦ ε`.
For closed subgroups of `GL_n` it also follows from
`AlgebraicGeometry.GeneralLinearGroup.tangentGroupMulEquiv` and
`AlgebraicGeometry.GeneralLinearGroup.dualUnit_add`.
(blueprint: `sk-d-tangent`) -/
instance : IsMulCommutative (tangentGroup G) :=
  sorry

variable {G} {H : Over (Spec (.of k))} [GrpObj H]

/-- A homomorphism of group schemes `f : G ⟶ H` maps tangent vectors to tangent vectors: if
`φ : Spec k[ε] ⟶ G` reduces to the identity, then so does `φ ≫ f`, since the diagram
```
Spec k ──(ε ↦ 0)──▶ Spec k[ε] ──φ──▶ G ──f──▶ H
   │                                 ▲        ▲
   └───────────────── 1 ─────────────┘        │
   └───────────────────── 1 ──────────────────┘
```
commutes and `f` maps `1` to `1`. -/
theorem comp_mem_tangentGroup (f : G ⟶ H) [IsMonHom f] {φ : points G (DualNumber k)}
    (hφ : φ ∈ tangentGroup G) : φ ≫ f ∈ tangentGroup H := by
  rw [mem_tangentGroup, pointsMap_apply] at hφ ⊢
  rw [← Category.assoc, hφ, MonObj.one_comp]

/-- The differential `T_1 G → T_1 H` of a homomorphism of group schemes `f : G ⟶ H`, given by
post-composition with `f` on dual-number points: it sends `φ` to the composite
```
Spec k[ε] ──φ──▶ G ──f──▶ H
```
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentGroupMap (f : G ⟶ H) [IsMonHom f] : tangentGroup G →* tangentGroup H :=
  ((IsMonHom.monoidHom f _).comp (tangentGroup G).subtype).codRestrict (tangentGroup H)
    fun φ ↦ comp_mem_tangentGroup f φ.2

@[simp]
theorem coe_tangentGroupMap_apply (f : G ⟶ H) [IsMonHom f] (φ : tangentGroup G) :
    (tangentGroupMap f φ : points H (DualNumber k)) = (φ : points G _) ≫ f :=
  rfl

end AlgebraicGeometry
