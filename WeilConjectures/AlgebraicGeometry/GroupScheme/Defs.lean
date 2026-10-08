/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Torsion subgroup schemes and isogenies

Following Mathlib, a group scheme over a base scheme `S` is an object `G` of `Over S` equipped
with `CategoryTheory.GrpObj G`, multiplication by `n` being the `n`-th power `𝟙 G ^ n` of the
identity in the group `G ⟶ G` of `CategoryTheory.GrpObj.Hom.group`. This file introduces the
`n`-torsion subgroup scheme, isogenies and their degree over an arbitrary base. The degree of
an isogeny is the rank of its finite locally free kernel, a locally constant function on the
base (`AlgebraicGeometry.isogenyDegreeAt`); over a field it is a number
(`AlgebraicGeometry.isogenyDegree`), the order `dim_K Γ(ker f, 𝒪)` of the kernel
(`AlgebraicGeometry.isogenyDegree_eq_finrank_Γ`).

## Main definitions

- `AlgebraicGeometry.torsionSubgroupScheme`: the `n`-torsion subgroup scheme `G[n]`.
  Being a kernel, it is itself a group scheme (`CategoryTheory.GrpObj.instGrpObjKer`).
- `AlgebraicGeometry.IsIsogeny`: a surjective homomorphism of group schemes with finite locally
  free kernel.
- `AlgebraicGeometry.isogenyDegreeAt`, `AlgebraicGeometry.isogenyDegree`: the degree of an
  isogeny at a point of the base, the rank of its kernel there, and its value over a field.

## Main statements

- `AlgebraicGeometry.isMonHom_npow_id`: the `n`-fold sum on a commutative group scheme is a
  homomorphism.
- `AlgebraicGeometry.isClosedImmersion_kerι`: the kernel of a homomorphism of group schemes is
  a closed subgroup scheme.
- `AlgebraicGeometry.isLocallyConstant_isogenyDegreeAt`: the degree of an isogeny is locally
  constant on the base.
- `AlgebraicGeometry.isogenyDegree_eq_finrank_Γ`: over a field the degree of an isogeny is the
  order of its kernel.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-hom`: The `n`-fold sum is a homomorphism.

Let `G` be a commutative group scheme over a base `S`. Then the `n`-fold sum map `[n] : G ⟶ G`
is a homomorphism of group schemes. -/
instance isMonHom_npow_id (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (𝟙 G ^ n) :=
  sorry

/-- Blueprint `sk-def-av-group-scheme`: Kernels are closed subgroup schemes.

The kernel of a homomorphism `f : A ⟶ B` of group schemes over a base `S` with `B` separated
over `S` is a closed subscheme of `A`: the unit section of a separated group scheme is a closed
immersion, and closed immersions are stable under base change. It is a subgroup scheme by
`CategoryTheory.GrpObj.instGrpObjKer` and `CategoryTheory.GrpObj.isMonHom_kerι`. -/
theorem isClosedImmersion_kerι {A B : Over S} [GrpObj A] [GrpObj B] [IsSeparated B.hom]
    (f : A ⟶ B) [IsMonHom f] :
    IsClosedImmersion (GrpObj.kerι f).left :=
  sorry

/-- Blueprint `sk-def-av-mult-n`: Multiplication by `n` and `n`-torsion.

The `n`-torsion subgroup scheme `G[n]` of a group scheme `G` over a base `S` is the kernel of
the `n`-th power map `𝟙 G ^ n`, which on points is `a ↦ a + ⋯ + a`:

```
  G[n] ──────────────▶ 𝟙_ (Over S)
    │                            │
    │                            │ η[G]
    ▼                            ▼
    G ───── 𝟙 G ^ n ───────────▶ G
```
-/
noncomputable def torsionSubgroupScheme (G : Over S) [GrpObj G] (n : ℕ) : Over S :=
  GrpObj.ker (𝟙 G ^ n)

/-- The `n`-torsion of a commutative group scheme is itself a group scheme, being a kernel. -/
noncomputable instance (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    GrpObj (torsionSubgroupScheme G n) :=
  inferInstanceAs (GrpObj (GrpObj.ker (𝟙 G ^ n)))

/-- Blueprint `sk-def-av-isogeny`: Isogenies and their degree.

An *isogeny* `f : A ⟶ B` of group schemes over a base `S` is a surjective homomorphism whose
kernel is finite locally free over `S`, that is finite, flat and locally of finite presentation.
The blueprint defines isogenies between abelian varieties, where the kernel of a surjective
homomorphism with finite kernel is automatically finite locally free; the definition makes
sense for arbitrary group schemes over any base, and it is the finite local freeness of the
kernel that makes its rank `AlgebraicGeometry.isogenyDegreeAt` a locally constant function on
`S`. It is only for abelian schemes that this is the degree of `f` itself as a finite flat
morphism (see `AlgebraicGeometry.IsIsogeny.finrank_eq`). -/
class IsIsogeny {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) : Prop
    extends IsMonHom f, Surjective f.left where
  /-- The kernel of an isogeny is a finite group scheme. -/
  isFinite_ker : IsFinite (GrpObj.ker f).hom
  /-- The kernel of an isogeny is flat over the base. -/
  flat_ker : Flat (GrpObj.ker f).hom
  /-- The kernel of an isogeny is locally of finite presentation over the base. -/
  locallyOfFinitePresentation_ker : LocallyOfFinitePresentation (GrpObj.ker f).hom

attribute [instance] IsIsogeny.isFinite_ker IsIsogeny.flat_ker
  IsIsogeny.locallyOfFinitePresentation_ker

/-- Blueprint `sk-def-av-isogeny`: Isogenies and their degree.

The degree of a homomorphism `f : A ⟶ B` of group schemes over `S` at a point `s : S`: the rank
`AlgebraicGeometry.Scheme.Hom.finrank` at `s` of the kernel of `f` over `S`, that is, the rank of
the `𝒪_{S, s}`-module `(𝒪_{ker f})_s`. For an isogeny the kernel is finite locally free, so
this is a locally constant function of `s`
(`AlgebraicGeometry.isLocallyConstant_isogenyDegreeAt`); for other homomorphisms it is a
number without meaning. -/
noncomputable def isogenyDegreeAt {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) (s : S) :
    ℕ :=
  (GrpObj.ker f).hom.finrank s

/-- The degree of an isogeny is a locally constant function on the base, the rank of a finite
locally free morphism being locally constant. -/
theorem isLocallyConstant_isogenyDegreeAt {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B)
    [IsIsogeny f] : IsLocallyConstant (isogenyDegreeAt f) :=
  (GrpObj.ker f).hom.isLocallyConstant_finrank

/-- Blueprint `sk-def-av-isogeny`: Isogenies and their degree.

The degree of a homomorphism `f : A ⟶ B` of group schemes over a field `K`: the value of
`AlgebraicGeometry.isogenyDegreeAt f` at the unique point of `Spec K`. For an isogeny it is the
order of the kernel (`AlgebraicGeometry.isogenyDegree_eq_finrank_Γ`). -/
noncomputable def isogenyDegree {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) :
    ℕ :=
  isogenyDegreeAt f default

/-- Over a field `K` the degree of an isogeny `f` is the order of its kernel, the `K`-dimension
of `Γ(ker f, 𝒪)`: the kernel is finite over `Spec K`, and the rank of a finite morphism to the
spectrum of a field at its unique point is the dimension of its ring of global sections
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_Γ`). -/
theorem isogenyDegree_eq_finrank_Γ {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B)
    [IsIsogeny f] :
    letI := (GrpObj.ker f).hom.ΓAlgebra
    isogenyDegree f = Module.finrank K Γ((GrpObj.ker f).left, ⊤) :=
  (GrpObj.ker f).hom.finrank_eq_finrank_Γ _

end AlgebraicGeometry
