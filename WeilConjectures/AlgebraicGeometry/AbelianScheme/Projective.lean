/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianScheme.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

/-!
# Abelian varieties are projective

An abelian variety is projective over its base field (`AlgebraicGeometry.IsProjective`, that is,
it admits a closed immersion into a projective space over the field), hence carries an ample
invertible module, and the symmetrisation `L ⊗ [-1]^* L` of an ample invertible
module is again ample and is symmetric.

The existence statements are specific to a field: an abelian scheme over a general base need
not be projective, and need not carry a relatively ample invertible module, even over a local
base (Raynaud's example, SGA 7 / LNM 119, XII 4.2: glue `E × ℙ¹` over the nodal curve obtained
from `ℙ¹` by identifying `0` and `∞`, along translation by a non-torsion point; any invertible
module on the result is translation-invariant on the fibre over the node, hence not ample
there). Over a normal base every abelian scheme is projective (Raynaud, LNM 119, XI 1.4), but
Mathlib has no notion of a normal scheme yet. The symmetrisation, its ampleness and its
symmetry make sense, and hold, over any base.

`AlgebraicGeometry.IsVeryAmple` is a genuine definition, and so is the tensor product
`AlgebraicGeometry.Scheme.Modules.tensorObj` (see
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), through whose tensor powers ampleness is
phrased. So `IsAbelianScheme.exists_isAmple` follows from `IsAbelianScheme.isProjective`, with
`M := j^* 𝒪(1)` for the closed immersion `j` provided by projectivity and the first tensor
power, together with the identification `M^{⊗ 1} ≅ M`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.symmetrisation`: the symmetrisation `L ⊗ [-1]^* L`.
- `AlgebraicGeometry.Scheme.Modules.overPullbackInvSymmetrisationIso`: the canonical
  isomorphism `[-1]^* (L ⊗ [-1]^* L) ≅ L ⊗ [-1]^* L`, exhibiting the symmetrisation as symmetric.

## Main statements

- `AlgebraicGeometry.IsAbelianScheme.isProjective`: abelian varieties are projective.
- `AlgebraicGeometry.IsAbelianScheme.exists_isAmple`: abelian varieties carry an ample
  invertible module.
- `AlgebraicGeometry.IsAbelianScheme.isAmple_symmetrisation`: `L ⊗ [-1]^* L` is relatively
  ample whenever `L` is.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {S : Scheme.{u}} {K : Type u} [Field K]

/-- The *symmetrisation* `L ⊗ [-1]^* L` of an invertible module `L` on a group scheme over a
base `S`: the smallest symmetric module built from `L`. -/
noncomputable def Scheme.Modules.symmetrisation {A : Over S} [GrpObj A]
    (L : A.left.Modules) : A.left.Modules :=
  tensorObj L (overPullback ι[A] L)

/-- Blueprint `sk-prop-av-projective`: Abelian varieties are projective.

Every abelian variety `A` over a field `K` is projective over `Spec K`, that is, it admits a
closed immersion into a projective space over `Spec K` compatible with the structure
morphisms. -/
instance IsAbelianScheme.isProjective (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    IsProjective A.hom :=
  sorry

/-- Blueprint `sk-prop-av-projective`: Abelian varieties are projective.

Being projective, an abelian variety over a field `K` carries an ample invertible
`𝒪_A`-module. This does not extend to abelian schemes over a general base, see the module
docstring. -/
theorem IsAbelianScheme.exists_isAmple (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianScheme A] :
    ∃ M : A.left.Modules, M.IsInvertible ∧ IsAmple A.hom M :=
  sorry

/-- Blueprint `sk-prop-av-symmetric-ample`: A symmetric ample module.

Let `A` be an abelian scheme over a base `S` and let `L` be a relatively ample invertible
`𝒪_A`-module. Then the symmetrisation `L ⊗ [-1]^* L` is relatively ample. In the blueprint `S`
is the spectrum of a field. -/
theorem IsAbelianScheme.isAmple_symmetrisation (A : Over S) [GrpObj A] [IsAbelianScheme A]
    (L : A.left.Modules) [L.IsInvertible] (hample : IsAmple A.hom L) :
    IsAmple A.hom L.symmetrisation :=
  sorry

/-- Blueprint `sk-prop-av-symmetric-ample`: A symmetric ample module.

The symmetrisation `N = L ⊗ [-1]^* L` of a module `L` on a group scheme `A` over a base `S` is
*symmetric*: the canonical isomorphism `[-1]^* N ≅ N`. It is the composite of the
compatibility of pullback with tensor products,
`[-1]^* (L ⊗ [-1]^* L) ≅ [-1]^* L ⊗ [-1]^* [-1]^* L`, of the identification
`[-1]^* [-1]^* L ≅ L` coming from `ι[A] ≫ ι[A] = 𝟙 A` together with
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackId`, and of the braiding of `A.left.Modules`. No
choice is involved, and neither `IsAbelianScheme A` nor invertibility of `L` is needed; the
blueprint states it for an ample invertible module on an abelian variety. -/
noncomputable def Scheme.Modules.overPullbackInvSymmetrisationIso {A : Over S} [GrpObj A]
    (L : A.left.Modules) : overPullback ι[A] L.symmetrisation ≅ L.symmetrisation :=
  sorry

end AlgebraicGeometry
