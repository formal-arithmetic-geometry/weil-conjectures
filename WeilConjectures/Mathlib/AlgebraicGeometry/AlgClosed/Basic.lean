/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Existence of a rational point

Over an algebraically closed field `K`, a nonempty `K`-scheme locally of finite type has a
`K`-rational point: its closed points are `K`-rational by
`AlgebraicGeometry.pointOfClosedPoint`, and it has a closed point because it is a Jacobson
space.

## Main results

- `AlgebraicGeometry.exists_comp_eq_id`: a nonempty scheme locally of finite type over an
  algebraically closed field `K` admits a section of its structure morphism.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- A nonempty scheme locally of finite type over an algebraically closed field `K` has a
`K`-rational point. -/
theorem exists_comp_eq_id (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [Nonempty X] :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (X := X) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact ⟨_, pointOfClosedPoint_comp f x hx⟩

end AlgebraicGeometry
