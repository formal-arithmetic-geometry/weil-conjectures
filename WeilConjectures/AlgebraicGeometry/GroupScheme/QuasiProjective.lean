/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# Group schemes of finite type over a field are quasi-projective

A group scheme of finite type over a field `k` is quasi-projective over `k` (Stacks 0BF7).
Over a field, quasi-projectivity amounts to an immersion into a projective space `ℙ(α; Spec k)`
with finitely many homogeneous coordinates, and this is the form in which it is stated here.

Following Stacks 0BF7, the statement is reduced to the case of an algebraically closed field:
the base change of `G` to an algebraic closure `K` of `k` is again a group scheme of finite type,
and quasi-projectivity descends from `K` to `k`
(`AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`, Stacks 0BDE).

## Main statements

- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`: the case of an
  algebraically closed field.
- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`: a group scheme of finite type
  over a field admits an immersion into a projective space over the field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Group schemes of finite type over an algebraically closed field are quasi-projective.**
A group scheme `G` of finite type over an algebraically closed field `k` admits an immersion
`G ⟶ ℙ(α; Spec k)` over `Spec k` into a projective space with finitely many homogeneous
coordinates.

This is the main case of Stacks 0BF7: one reduces to `G` connected, then to `G` smooth by
passing to `G_red`, and for `G` smooth and connected one constructs an ample invertible module
from an effective Cartier divisor with affine complement. It is the input of
`AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`, used for blueprint
`lem-sc-abelian-variety-projective` and the subsection `sk-prop-av-projective`. -/
theorem GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom :=
  sorry

/-- **Group schemes of finite type over a field are quasi-projective.** A group scheme `G` of
finite type over a field `k` admits an immersion `G ⟶ ℙ(α; Spec k)` over `Spec k` into a
projective space with finitely many homogeneous coordinates.

The base change of `G` to an algebraic closure of `k` is a group scheme of finite type over an
algebraically closed field, hence quasi-projective
(`AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`), and
quasi-projectivity descends along field extensions (Stacks 0BDE).

This is the input (Stacks 0BF7) used in the proof of blueprint `lem-sc-abelian-variety-projective`
and of the subsection `sk-prop-av-projective`. -/
@[stacks 0BF7]
theorem GrpObj.exists_isImmersion_projectiveSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (Limits.pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have : LocallyOfFiniteType (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : QuasiCompact (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.hom g))
  obtain ⟨α, _, j, hj, hjG⟩ :=
    exists_isImmersion_projectiveSpace_of_isAlgClosed (Over.mk (Limits.pullback.snd G.hom g))
  exact exists_isImmersion_projectiveSpace_of_pullback G.hom j hjG

end AlgebraicGeometry
