/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Torsion subgroup schemes and isogenies

Following Mathlib, a group scheme over a field `K` is an object `G` of `Over (Spec (.of K))`
equipped with `CategoryTheory.GrpObj G`, multiplication by `n` being the `n`-th power `𝟙 G ^ n`
of the identity in the group `G ⟶ G` of `CategoryTheory.GrpObj.Hom.group`. This file introduces
the `n`-torsion subgroup scheme and isogenies; the order of a finite group scheme over `K` is
`AlgebraicGeometry.Scheme.Hom.finrankΓ` of its structure morphism.

## Main definitions

- `AlgebraicGeometry.torsionSubgroupScheme`: the `n`-torsion subgroup scheme `G[n]`.
  Being a kernel, it is itself a group scheme (`CategoryTheory.GrpObj.instGrpObjKer`).
- `AlgebraicGeometry.torsionByEquiv`: the `K`-points of `G[n]` are the `n`-torsion of `G(K)`.
- `AlgebraicGeometry.IsIsogeny`: a surjective homomorphism of group schemes with finite kernel.
- `AlgebraicGeometry.isogenyDegree`: the degree of an isogeny, the order of its kernel.

## Main statements

- `AlgebraicGeometry.isMonHom_npow_id`: the `n`-fold sum on a commutative group scheme is a
  homomorphism.
- `AlgebraicGeometry.isClosedImmersion_kerι`: the kernel of a homomorphism of group schemes is
  a closed subgroup scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-hom`: The `n`-fold sum is a homomorphism.

Let `G` be a commutative group scheme over `K`. Then the `n`-fold sum map `[n] : G ⟶ G` is a
homomorphism of group schemes: it is the `n`-th power of the homomorphism `𝟙 G` in the
commutative monoid `G ⟶ G`, and such powers are homomorphisms
(`CategoryTheory.MonObj.isMonHom_pow`, blueprint `lem-sc-mult-n-homomorphism`). -/
instance isMonHom_npow_id (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (𝟙 G ^ n) :=
  MonObj.isMonHom_pow _ n

/-- Blueprint `sk-def-av-group-scheme`: Kernels are closed subgroup schemes.

The kernel of a homomorphism `f : A ⟶ B` of group schemes over `K` with `B` separated is a
closed subscheme of `A`: the unit section of a separated group scheme is a closed immersion,
and closed immersions are stable under base change. It is a subgroup scheme by
`CategoryTheory.GrpObj.instGrpObjKer` and `CategoryTheory.GrpObj.isMonHom_kerι`. -/
theorem isClosedImmersion_kerι {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    [IsSeparated B.hom] (f : A ⟶ B) [IsMonHom f] :
    IsClosedImmersion (GrpObj.kerι f).left :=
  sorry

/-- Blueprint `sk-def-av-mult-n`: Multiplication by `n` and `n`-torsion.

The `n`-torsion subgroup scheme `G[n]` of a group scheme `G` over `K` is the kernel of the
`n`-th power map `𝟙 G ^ n`, which on points is `a ↦ a + ⋯ + a`:

```
  G[n] ──────────────▶ 𝟙_ (Over (Spec (.of K)))
    │                            │
    │                            │ η[G]
    ▼                            ▼
    G ───── 𝟙 G ^ n ───────────▶ G
```
-/
noncomputable def torsionSubgroupScheme (G : Over (Spec (.of K))) [GrpObj G] (n : ℕ) :
    Over (Spec (.of K)) :=
  GrpObj.ker (𝟙 G ^ n)

/-- The `n`-torsion of a commutative group scheme is itself a group scheme, being a kernel. -/
noncomputable instance (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    GrpObj (torsionSubgroupScheme G n) :=
  inferInstanceAs (GrpObj (GrpObj.ker (𝟙 G ^ n)))

/-- The `K`-points of the `n`-torsion subgroup scheme `G[n]` of a commutative group scheme `G`
are the `n`-torsion points of `G`: the `n`-torsion of the group `G(K)`, written additively, is
in bijection with `𝟙_ (Over (Spec (.of K))) ⟶ G[n]`, a point `x` of `G[n]` corresponding to
its image `x ≫ GrpObj.kerι (𝟙 G ^ n)` in `G(K)`. -/
noncomputable def torsionByEquiv (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ G)) (n : ℤ) ≃
      (𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme G n) :=
  (Equiv.subtypeEquiv (p := fun x ↦ x ∈ AddSubgroup.torsionBy _ (n : ℤ))
    (q := fun x ↦ x ∈ MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ n) (𝟙_ _))) Additive.toMul
    fun x ↦ by
      rw [MonoidHom.mem_ker, AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup,
        Submodule.mem_torsionBy_iff, natCast_zsmul]
      change n • x = 0 ↔ x.toMul ≫ 𝟙 G ^ n = 1
      rw [comp_pow, Category.comp_id]
      rfl).trans (GrpObj.kerRepresentableBy (𝟙 G ^ n)).homEquiv.symm

/-- Blueprint `sk-def-av-isogeny`: Isogenies and their degree.

An *isogeny* `f : A ⟶ B` of group schemes over `K` is a surjective homomorphism with finite
kernel. The blueprint defines isogenies between abelian varieties; the definition makes sense
for arbitrary group schemes, but it is only for abelian varieties that
`AlgebraicGeometry.isogenyDegree` is the degree of `f` as a finite flat morphism (see
`AlgebraicGeometry.IsIsogeny.finrank_eq`). -/
class IsIsogeny {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) : Prop
    extends IsMonHom f, Surjective f.left where
  /-- The kernel of an isogeny is a finite group scheme. -/
  isFinite_ker : IsFinite (GrpObj.ker f).hom

attribute [instance] IsIsogeny.isFinite_ker

/-- The degree of an isogeny `f : A ⟶ B`: the order of its kernel.

This is only the degree of `f` as a finite flat morphism when `f` is an isogeny of abelian
varieties; outside that range it is the order of the kernel and nothing more. -/
noncomputable def isogenyDegree {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) :
    ℕ :=
  (GrpObj.ker f).hom.finrankΓ

end AlgebraicGeometry
