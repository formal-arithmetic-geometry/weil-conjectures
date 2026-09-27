/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

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
- `AlgebraicGeometry.IsIsogeny`: a surjective homomorphism of group schemes with finite kernel.
- `AlgebraicGeometry.isogenyDegree`: the degree of an isogeny, the order of its kernel.

## Main statements

- `AlgebraicGeometry.isMonHom_npow_id`: the `n`-fold sum on a commutative group scheme is a
  homomorphism.
- `AlgebraicGeometry.isClosedImmersion_kerι`: the kernel of a homomorphism of group schemes is
  a closed subgroup scheme.
- `AlgebraicGeometry.fiberDegree_eq_finrankΓ`: the order of a group scheme over a field is the
  fibre degree of its structure morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-hom`: The `n`-fold sum is a homomorphism.

Let `G` be a commutative group scheme over `K`. Then the `n`-fold sum map `[n] : G ⟶ G` is a
homomorphism of group schemes. -/
instance isMonHom_npow_id (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (𝟙 G ^ n) :=
  sorry

/-- Blueprint `sk-def-av-group-scheme`: Kernels are closed subgroup schemes.

The kernel of a homomorphism `f : A ⟶ B` of group schemes over `K` with `B` separated is a
closed subscheme of `A`: the unit section of a separated group scheme is a closed immersion,
and closed immersions are stable under base change. It is a subgroup scheme by
`CategoryTheory.GrpObj.instGrpObjKer` and `CategoryTheory.GrpObj.isMonHom_kerι`. -/
theorem isClosedImmersion_kerι {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    [IsSeparated B.hom] (f : A ⟶ B) [IsMonHom f] :
    IsClosedImmersion (GrpObj.kerι f).left :=
  sorry

/-- The order `f.finrankΓ` of a finite group scheme over a field is the fibre degree of its
structure morphism at the unique point of `Spec K`; the two degree notions of the project agree
on group schemes over a field.

This is a statement about an arbitrary affine morphism to the spectrum of a field, so it belongs
in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; it is stated here only to keep
that file free of `sorry`. -/
theorem fiberDegree_eq_finrankΓ {G : Scheme.{u}} (f : G ⟶ Spec (.of K)) [IsAffineHom f]
    (x : Spec (.of K)) :
    f.fiberDegree x = f.finrankΓ :=
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
