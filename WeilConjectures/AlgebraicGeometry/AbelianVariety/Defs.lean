/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Abelian varieties: the basic definitions

Following Mathlib, a group scheme over a field `K` is an object `A` of `Over (Spec (.of K))`
equipped with `CategoryTheory.GrpObj A`. This file introduces the notions attached to such an
`A` that the abelian-variety block of the blueprint rests on: the order of a finite group
scheme, abelian varieties themselves, the multiplication-by-`n` torsion subgroup scheme, and
isogenies.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.finrankΓ`: the `R`-dimension of the global sections of a
  scheme over `Spec R`. For a finite group scheme over a field this is its *order*.
- `AlgebraicGeometry.IsAbelianVariety`: a group scheme over `K` which is proper, smooth and
  connected.
- `AlgebraicGeometry.torsionSubgroupScheme`: the `n`-torsion subgroup scheme `A[n]`.
- `AlgebraicGeometry.IsIsogeny`: a surjective homomorphism of group schemes with finite kernel.
- `AlgebraicGeometry.isogenyDegree`: the degree of an isogeny, the order of its kernel.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The `R`-dimension of the ring of global sections of a scheme over `Spec R`.

Blueprint `sk-def-av-group-scheme`: Group schemes, order, and étaleness. For a finite group
scheme `G` over a field `K` this is the *order* `|G| = dim_K Γ(G, 𝒪_G)`. -/
noncomputable def Scheme.Hom.finrankΓ {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    ℕ :=
  letI := f.ΓAlgebra
  Module.finrank R Γ(X, ⊤)

/-- Blueprint `sk-def-av`: Abelian varieties.

An *abelian variety* over a field `K` is a group scheme over `K` which is proper, smooth and
connected; its *dimension* is the Krull dimension of its underlying space. -/
class IsAbelianVariety (A : Over (Spec (.of K))) [GrpObj A] : Prop where
  isProper : IsProper A.hom
  smooth : Smooth A.hom
  connectedSpace : ConnectedSpace A.left

attribute [instance] IsAbelianVariety.isProper IsAbelianVariety.smooth
  IsAbelianVariety.connectedSpace

/-- Blueprint `sk-def-av-mult-n`: Multiplication by `n` and `n`-torsion.

The `n`-torsion subgroup scheme `A[n]` of a group scheme `A` over `K` is the kernel of the
`n`-th power map `𝟙 A ^ n`, which on points is `a ↦ a + ⋯ + a`. -/
noncomputable def torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A] (n : ℕ) :
    Over (Spec (.of K)) :=
  GrpObj.ker (𝟙 A ^ n)

/-- Blueprint `sk-def-av-isogeny`: Isogenies and their degree.

An *isogeny* `f : A ⟶ B` of group schemes over `K` is a surjective homomorphism with finite
kernel. -/
structure IsIsogeny {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) : Prop where
  isMonHom : IsMonHom f
  surjective : Surjective f.left
  isFinite_ker : IsFinite (GrpObj.ker f).hom

/-- The degree of an isogeny `f : A ⟶ B`: the order of its kernel. -/
noncomputable def isogenyDegree {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) :
    ℕ :=
  (GrpObj.ker f).hom.finrankΓ

end AlgebraicGeometry
