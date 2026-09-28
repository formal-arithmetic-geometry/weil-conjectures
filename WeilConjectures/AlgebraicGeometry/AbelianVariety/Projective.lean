/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Abelian varieties are projective

An abelian variety admits a closed immersion into a projective space over the base field, hence
carries an ample invertible module, and the symmetrisation `L ⊗ [-1]^* L` of an ample invertible
module is again ample and is symmetric.

Since `AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.Scheme.Modules.tensorObj` are still
`opaque` placeholders (see `WeilConjectures.AlgebraicGeometry.Modules.Ample` and
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), none of the statements below can be
proved before those are replaced by real constructions.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.symmetrisation`: the symmetrisation `L ⊗ [-1]^* L`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.exists_isClosedImmersion_projectiveSpace`: abelian
  varieties are projective.
- `AlgebraicGeometry.IsAbelianVariety.exists_isAmple`: abelian varieties carry an ample
  invertible module.
- `AlgebraicGeometry.IsAbelianVariety.isAmple_symmetrisation`,
  `AlgebraicGeometry.IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation`:
  `L ⊗ [-1]^* L` is ample and symmetric.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- The *symmetrisation* `L ⊗ [-1]^* L` of an invertible module `L` on a group scheme: the
smallest symmetric module built from `L`. -/
noncomputable def Scheme.Modules.symmetrisation {A : Over (Spec (.of K))} [GrpObj A]
    (L : A.left.Modules) : A.left.Modules :=
  tensorObj L (overPullback ι[A] L)

/-- Blueprint `sk-prop-av-projective`: Abelian varieties are projective.

Every abelian variety `A` over a field `K` admits a closed immersion into a projective space
over `Spec K` compatible with the structure morphisms. The index type of the projective space
is called `α`; `ι`, the usual name for an index type, is unavailable as an identifier here,
being the token of the inversion notation `ι[A]`. -/
theorem IsAbelianVariety.exists_isClosedImmersion_projectiveSpace (A : Over (Spec (.of K)))
    [GrpObj A] [IsAbelianVariety A] :
    ∃ (α : Type u) (_ : Finite α) (j : A.left ⟶ ℙ(α; Spec (.of K))),
      IsClosedImmersion j ∧ j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K) = A.hom :=
  sorry

/-- Blueprint `sk-prop-av-projective`: Abelian varieties are projective.

Being projective, an abelian variety carries an ample invertible `𝒪_A`-module. -/
theorem IsAbelianVariety.exists_isAmple (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] :
    ∃ M : A.left.Modules, M.IsInvertible ∧ IsAmple A.hom M :=
  sorry

/-- Blueprint `sk-prop-av-symmetric-ample`: A symmetric ample module.

Let `A` be an abelian variety over `K` and let `L` be an ample invertible `𝒪_A`-module. Then the
symmetrisation `L ⊗ [-1]^* L` is ample. -/
theorem IsAbelianVariety.isAmple_symmetrisation (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (L : A.left.Modules) [L.IsInvertible] (hample : IsAmple A.hom L) :
    IsAmple A.hom L.symmetrisation :=
  sorry

/-- Blueprint `sk-prop-av-symmetric-ample`: A symmetric ample module.

The symmetrisation `N = L ⊗ [-1]^* L` of an invertible module on an abelian variety is
*symmetric*, that is `[-1]^* N ≅ N`. -/
theorem IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (L : A.left.Modules)
    [L.IsInvertible] :
    Nonempty (overPullback ι[A] L.symmetrisation ≅ L.symmetrisation) :=
  sorry

end AlgebraicGeometry
