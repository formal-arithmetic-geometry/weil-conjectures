/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData

/-! # Coefficient descent for right refinement mates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- A left coefficient square gives the right square for the same fixed adjunctions.
Source: adjunction transposition, Zheng 2.23 and 2.29
(blueprint: lem-sf-exceptional-refinement-right-square).

Proof: cancel the invertible comparison b.b.hom and apply the injective inverse Hom
bijection for A'. Move a.b.hom and b.b.hom through the two coefficient counit equations.
Naturality of a.q.inv and the counit equation for p replace the old right refinement
by the old left refinement. The assumed left square replaces this by q.left. Naturality
of q.left and the counit equation for q identify the result with the transpose of its
right refinement. No invertibility or naturality of an evaluated geometric map is used. -/
theorem right_coefficient_square_of_left {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A B : Operation.{u, v} l Ω X Y s) (A' B' : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t)
    (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    (a : FieldComparison.{u, v} l Ω A A' TX TY)
    (b : FieldComparison.{u, v} l Ω B B' TX TY)
    (p : RefinementComparison.{u, v} l Ω A B)
    (q : RefinementComparison.{u, v} l Ω A' B')
    (h : ∀ K, a.q.inv.app K ≫ TY.map (p.left.hom.app K) ≫ b.q.hom.app K =
      q.left.hom.app (TX.obj K)) (L : C.{u, v} l Ω Y s) :
    b.b.inv.app L ≫ TX.map (p.right.hom.app L) ≫ a.b.hom.app L =
      q.right.hom.app (TY.obj L) := by
  have ac : A'.F.map (a.b.hom.app L) ≫ A'.adjunction.counit.app (TY.obj L) =
      a.q.inv.app (A.G.obj L) ≫ TY.map (A.adjunction.counit.app L) := by
    let := a.shiftX
    let := a.shiftY
    rw [← a.comparison.counit L]
    simp only [FieldComparison.q, FieldComparison.b, Iso.inv_hom_id_app_assoc]
  have bc : B'.F.map (b.b.hom.app L) ≫ B'.adjunction.counit.app (TY.obj L) =
      b.q.inv.app (B.G.obj L) ≫ TY.map (B.adjunction.counit.app L) := by
    let := b.shiftX
    let := b.shiftY
    rw [← b.comparison.counit L]
    simp only [FieldComparison.q, FieldComparison.b, Iso.inv_hom_id_app_assoc]
  have hn := a.q.inv.naturality (p.right.hom.app L)
  dsimp only [Functor.comp_map] at hn
  have hl : a.q.inv.app (B.G.obj L) ≫ TY.map (p.left.hom.app (B.G.obj L)) =
      q.left.hom.app (TX.obj (B.G.obj L)) ≫ b.q.inv.app (B.G.obj L) := by
    rw [← h]
    simp [Category.assoc]
  apply (cancel_epi (b.b.hom.app L)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  apply (A'.adjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [ac, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← TY.map_comp, ← p.counit L, TY.map_comp]
  rw [← Category.assoc, hl, Category.assoc, ← bc]
  rw [← q.counit, ← Category.assoc, ← q.left.hom.naturality]
  simp only [Functor.comp_obj, Category.assoc]


end WeilConjectures.ExceptionalRefinement
