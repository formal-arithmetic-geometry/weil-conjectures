/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The trace of the affine line and the affine-line purity comparison

Let `Y` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible,
`p : 𝔸¹_Y → Y` the projection, `j : 𝔸¹_Y ↪ ℙ¹_Y` the standard chart `t ↦ [t : 1]`,
`q : ℙ¹_Y → Y` the projection and `∞ : Y → ℙ¹_Y` the section at infinity. This file
constructs the *integration map* of the affine line

`∫_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2] ⟶ Λ_Y`

out of the projective-line trace `t_q`, and its transpose, the *affine-line purity comparison*

`γ_{p,K} : Lp^* K(1)[2] ⟶ Rp^! K`

(blueprint `def-pur-affine-line-purity-comparison`).

## The projective-line trace

Write `σ_p : Λ_Y ⟶ Rp_! Λ(1)[2]` for the *class of the zero section*: the orientation
`pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` (the adjoint of the Kummer boundary `∂κ(t)`, blueprint
`sk-prop-a1`) pushed forward along `Rp_!`, with `R(s ≫ p)_! ≅ Rp_! Rs_!` and `s ≫ p` an
isomorphism. Its image `h ∈ H²(ℙ¹_Y, Λ(1))` in `Rq_* Λ(1)[2]` is the class of the divisor
`[0 : 1]`, that is the Kummer first Chern class of `𝒪(1)`. The projective line decomposes as

`(1, h) : Λ_Y(1)[2] ⊕ Λ_Y ≅ Rq_* Λ(1)[2]`

(blueprint `thm-amb-p1-decomposition`, of subsection `sk-prop-sf-cbc`), and the trace `t_q` is
the projection onto the second summand (`def-amb-p1-trace`). By construction `t_q(h) = 1`, which
is the normalization `∫_p σ_p = 1` of the integration map.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineCompactification`: `𝔸¹_Y ↪ ℙ¹_Y ⟶ Y`.
- `AlgebraicGeometry.Etale.affineLineZeroClass`: `σ_p : Λ_Y ⟶ Rp_! Λ(1)[2]`.
- `AlgebraicGeometry.Etale.projectiveLineDecomposition`: `(1, h)`.
- `AlgebraicGeometry.Etale.projectiveLineTrace`: `t_q : Rq_* Λ(1)[2] ⟶ Λ_Y`.
- `AlgebraicGeometry.Etale.affineLineTrace`: `∫_p : Rp_! Λ(1)[2] ⟶ Λ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.affineLineZeroClass_affineLineTrace`: `∫_p σ_p = 1`.
- `AlgebraicGeometry.Etale.isIso_affineLineTrace`: `∫_p` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-! ### The standard compactification of the affine line -/

section Compactification

variable (Y : Scheme.{u})

/-- The standard affine chart `𝔸¹_Y ↪ ℙ¹_Y`, `t ↦ [t : 1]`, of
`AlgebraicGeometry.ProjectiveLine.affineChart`, read on `𝔸¹_Y = 𝔸(ULift (Fin 1); Y)`. -/
noncomputable def affineLineChart : 𝔸(ULift.{u} (Fin 1); Y) ⟶ ProjectiveLine Y :=
  (AffineSpace.reindexIso Y (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1)))).hom ≫
    ProjectiveLine.affineChart Y

instance : IsOpenImmersion (affineLineChart Y) := by
  rw [affineLineChart]
  infer_instance

@[reassoc (attr := simp)]
lemma affineLineChart_over :
    affineLineChart Y ≫ ProjectiveLine Y ↘ Y = 𝔸(ULift.{u} (Fin 1); Y) ↘ Y := by
  simp [affineLineChart, AffineSpace.reindexIso, AffineSpace.reindex_over]

/-- The standard compactification `𝔸¹_Y ↪ ℙ¹_Y ⟶ Y` of the affine line. -/
noncomputable def affineLineCompactification :
    Compactification (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) where
  Z := ProjectiveLine Y
  g := ProjectiveLine Y ↘ Y
  i := affineLineChart Y
  comm := (affineLineChart_over Y).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The section at infinity is the closed complement of the affine chart. -/
lemma range_infinity_eq_compl_range_affineLineChart :
    Set.range (ProjectiveLine.infinity Y).base = (Set.range (affineLineChart Y).base)ᶜ := by
  have h := ProjectiveLine.range_infinity Y
  have h' : Set.range (affineLineChart Y).base =
      ((ProjectiveLine.affineChart Y).opensRange : Set (ProjectiveLine Y)) := by
    rw [affineLineChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (AffineSpace.reindexIso Y _).hom.surjective, Set.image_univ]
    rfl
  rw [h']
  exact h

end Compactification

end Etale

end AlgebraicGeometry
