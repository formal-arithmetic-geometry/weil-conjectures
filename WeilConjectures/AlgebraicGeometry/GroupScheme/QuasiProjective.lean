/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Group schemes of finite type over a field are quasi-projective

A group scheme of finite type over a field `k` is quasi-projective over `k` (Stacks 0BF7).
Over a field, quasi-projectivity amounts to an immersion into a projective space `ℙ(α; Spec k)`
with finitely many homogeneous coordinates, and this is the form in which it is stated here.

## Main statements

- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`: a group scheme of finite type
  over a field admits an immersion into a projective space over the field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Group schemes of finite type over a field are quasi-projective.** A group scheme `G` of
finite type over a field `k` admits an immersion `G ⟶ ℙ(α; Spec k)` over `Spec k` into a
projective space with finitely many homogeneous coordinates.

This is the input (Stacks 0BF7) used in the proof of blueprint `lem-sc-abelian-variety-projective`
and of the subsection `sk-prop-av-projective`. -/
@[stacks 0BF7]
theorem GrpObj.exists_isImmersion_projectiveSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom :=
  sorry

end AlgebraicGeometry
