/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Quasi-projectivity descends along field extensions

Over a field `k`, a scheme `X` is quasi-projective precisely when it admits an immersion over
`Spec k` into a projective space `ℙ(β; Spec k)` with finitely many homogeneous coordinates; this
is the form in which quasi-projectivity is phrased here.

## Main definitions

- `AlgebraicGeometry.IsQuasiProjective`: a scheme over a field is quasi-projective if it admits
  an immersion into a projective space.

## Main statements

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`: if the base change `X_K`
  of a `k`-scheme `X` to a field extension `K / k` is quasi-projective over `K`, then `X` is
  quasi-projective over `k` (Stacks 0BDE).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A scheme `X` over a field `k`, with structure morphism `f`, is *quasi-projective* if it
admits an immersion over `Spec k`, that is a locally closed immersion, into a projective space
`ℙ(β; Spec k)` with finitely many homogeneous coordinates; equivalently, an open immersion into
a closed subscheme of such a projective space. (blueprint: `def-sc-quasi-projective`) -/
def IsQuasiProjective {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop :=
  ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
    IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f

/-- **Quasi-projectivity descends along field extensions** (Stacks 0BDE). Let `K / k` be a field
extension and let `X` be a scheme over `k`. If the base change `X_K` admits an immersion over
`Spec K` into a projective space `ℙ(α; Spec K)` with finitely many homogeneous coordinates, then
`X` admits an immersion over `Spec k` into a projective space `ℙ(β; Spec k)` with finitely many
homogeneous coordinates.

This is an input to the proof of Stacks 0BF7 (`AlgebraicGeometry.GrpObj.exists_isImmersion_
projectiveSpace`), used for blueprint `lem-sc-abelian-variety-projective` and the subsection
`sk-prop-av-projective`. -/
@[stacks 0BDE]
theorem exists_isImmersion_projectiveSpace_of_pullback {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {α : Type u} [Finite α]
    (j : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ ℙ(α; Spec (.of K)))
    [IsImmersion j] (hj : j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K) = pullback.snd _ _) :
    ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
      IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f :=
  sorry

end AlgebraicGeometry
