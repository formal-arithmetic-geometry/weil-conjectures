/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# The Picard functor and the Picard scheme of a curve

For a morphism of schemes `f : X ⟶ S` the *Picard functor* `Pic_{X/S}` is the fppf
sheafification of the Picard presheaf `T ↦ Pic (X ×[S] T)` on the category of schemes over
`S`.  We define it as `AlgebraicGeometry.picardFunctor` and state the theorem that for a
smooth projective curve `X` over a separably closed field `k` the Picard functor `Pic_{X/k}`
is representable by a group scheme over `k`.

## Main definitions

- `AlgebraicGeometry.picardFunctor`: the Picard functor of a morphism of schemes, as an fppf
  sheaf on the category of schemes over the base (blueprint `def:pc-picard-functor`).

## Main results

- `AlgebraicGeometry.isRepresentable_picardFunctor`: for a smooth projective curve over a
  separably closed field, the Picard functor is representable by a group scheme over the base
  field (blueprint `thm:pc-picard-representable`, Stacks 0B9Z).  The proof is not formalized
  yet.

## Implementation notes

A group scheme over `k` is a group object in the category of schemes over `Spec k`, that is a
term of `CategoryTheory.Grp (Over (Spec (.of k)))`, and "representable" is
`CategoryTheory.Functor.RepresentableBy` applied to the underlying presheaf of the
sheafification.  Since the Picard presheaf takes values in `Type (u + 1)` (no smallness of
the Picard group is claimed), the representing object and the represented functor live in
different universes; `RepresentableBy` is stated with independent universes and accommodates
this.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The **Picard functor** `Pic_{X/S}` of a morphism of schemes `f : X ⟶ S`: the fppf
sheafification of the Picard presheaf `T ↦ Pic (X ×[S] T)` on the category of schemes
over `S`.
(blueprint: `def:pc-picard-functor`, Stacks 0B9L) -/
@[stacks 0B9L]
noncomputable def picardFunctor (f : X ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf _ _).obj (picardPresheaf f)

/-- **The Picard scheme of a curve.** If `k` is a separably closed field and `X` is a smooth
projective curve over `k`, then the Picard functor `Pic_{X/k}` is representable, and the
representing scheme is a group scheme over `k`.
(blueprint: `thm:pc-picard-representable`, Stacks 0B9Z) -/
@[stacks 0B9Z]
theorem isRepresentable_picardFunctor {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSmoothProjectiveCurve f] :
    ∃ G : Grp (Over (Spec (.of k))), Nonempty ((picardFunctor f).obj.RepresentableBy G.X) := by
  sorry

end AlgebraicGeometry
