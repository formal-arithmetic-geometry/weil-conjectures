/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite local dimension for finite type schemes over a field

Source: Stacks Project, Algebra, Tag 00P1 (lemma-dimension-at-a-point-finite-type-field),
with the affine stalk calculation and the Noetherian local finiteness consequence of Tag 00KQ
(proposition-dimension) (blueprint: lem-kun-finite-type-local-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The local ring at any point of a finite type scheme over a field has finite Krull dimension.
Source: Stacks Project, Tags 00P1 and 00KQ
(blueprint: lem-kun-finite-type-local-dimension).

Proof:
A field is Noetherian, so its spectrum is locally Noetherian. Apply
`LocallyOfFiniteType.isLocallyNoetherian` to the structure morphism to obtain that `X`
is locally Noetherian. Mathlib's stalk instance, proved by localization on an affine
neighbourhood, makes `X.presheaf.stalk x` Noetherian. It is local because `X` is a scheme.
The Noetherian local ring instance from Krull's height theorem supplies
`FiniteRingKrullDim`, and `ringKrullDim_lt_top` gives the conclusion. -/
theorem ringKrullDim_stalk_lt_top_of_finiteType
    (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (x : X) : ringKrullDim (X.presheaf.stalk x) < ⊤ := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  exact ringKrullDim_lt_top

end AlgebraicGeometry
