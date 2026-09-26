/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Basic properties of abelian varieties

An abelian variety, defined as a proper smooth connected group scheme over a field, is
automatically irreducible and geometrically integral, it is projective, and it carries a
symmetric ample invertible module.

## Main statements

- `AlgebraicGeometry.geometricallyIntegral_of_isAbelianVariety`: abelian varieties are exactly
  the complete group varieties.
- `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_isAbelianVariety`: abelian
  varieties are projective.
- `AlgebraicGeometry.isAmple_tensorObj_overPullback_inv`: `L ⊗ [-1]^* L` is ample and symmetric.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

Let `G` be a group scheme over a field `K` which is proper, connected and smooth over `K`, that
is, an abelian variety in the sense of `AlgebraicGeometry.IsAbelianVariety`. Then `G` is
irreducible and geometrically integral. Conversely every abelian variety is a proper connected
smooth group scheme, by definition; hence "abelian variety" and "complete group variety"
describe the same class. -/
theorem geometricallyIntegral_of_isAbelianVariety (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianVariety G] :
    IrreducibleSpace G.left ∧ GeometricallyIntegral G.hom :=
  sorry

/-- Blueprint `sk-prop-av-projective`: Abelian varieties are projective.

Every abelian variety `A` over a field `K` is projective over `K`, that is, it admits a closed
immersion into a projective space over `Spec K` compatible with the structure morphisms; in
particular `A` carries an ample invertible `𝒪_A`-module. -/
theorem exists_isClosedImmersion_projectiveSpace_of_isAbelianVariety (A : Over (Spec (.of K)))
    [GrpObj A] [IsAbelianVariety A] :
    (∃ (n : Type u) (_ : Finite n) (j : A.left ⟶ ℙ(n; Spec (.of K))),
        IsClosedImmersion j ∧ j ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K) = A.hom) ∧
      ∃ M : A.left.Modules, M.IsInvertible ∧ IsAmple A.hom M :=
  sorry

/-- Blueprint `sk-prop-av-symmetric-ample`: A symmetric ample module.

Let `A` be an abelian variety over `K` and let `L` be an ample invertible `𝒪_A`-module. Then
`N := L ⊗ [-1]^* L` is ample and *symmetric*, that is `[-1]^* N ≅ N`. -/
theorem isAmple_tensorObj_overPullback_inv (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (L : A.left.Modules) (hL : L.IsInvertible) (hample : IsAmple A.hom L) :
    IsAmple A.hom (tensorObj L (overPullback ι[A] L)) ∧
      Nonempty (overPullback ι[A] (tensorObj L (overPullback ι[A] L)) ≅
        tensorObj L (overPullback ι[A] L)) :=
  sorry

end AlgebraicGeometry
