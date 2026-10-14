/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.Basic

/-!
# Finite relation factorization at a stage of a flat colimit

Source: Stacks Project, Tags 00HK and 00R6, equational flatness and finite-data descent.
(blueprint: lem-weil-pbc-colimit-flat-relation-descent)
-/

@[expose] public section

universe u v w z t
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

/-- A relation from a stage becomes a trivial relation at a later stage.
Source: Stacks Project, Tags 00HK and 00R6.
(blueprint: lem-weil-pbc-colimit-flat-relation-descent)

Proof: Map the given relation to N_infty. The compatibility of psi with phi
and of the module coprojections with the scalar actions gives a relation
with coefficients a_i(a_p) in A_infty. Flatness and the equational criterion
00HK give finitely many coefficients c_pq in A_infty and elements y_q in
N_infty, with n_i(x_p)=sum_q c_pq*y_q and sum_p a_i(a_p)*c_pq=0.
Represent the finitely many coefficients and module elements at stages of the
ring and additive-group colimits, and move all representatives to one stage
above i by directedness. Scalar compatibility identifies the images of the
stage expressions with these expressions in N_infty. Eventual zero in the
ring colimit makes all column relations zero at a common later stage, and
eventual equality in the additive-group colimit makes all row expressions
equal there. Move both sets of equations to a further common stage; ring
maps, additive maps and scalar compatibility preserve them. These descended
coefficients and vectors give the stated factorization. Empty row or column
sets are allowed, with empty sums equal to zero. No tensor-colimit or finite
presentation theorem, nor Noetherian or local hypothesis, is needed. -/
-- STATEMENT-DISPUTED: For independent indexing and ring universes, HasColimit A does
-- not supply elementwise ring equality descent; a categorical colimit in the smaller
-- ring universe need not be the algebraic direct limit. See report.md for a valuation
-- domain counterexample and the proved, explicitly elementwise variant.
theorem exists_stage_flat_relation_factorization
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z}))
    (i : Λ) {ι : Type t} [Fintype ι] (a : ι → A.obj i) (x : ι → N.obj i)
    (hx : ∑ p, (φ i) (a p) • x p = 0) :
    ∃ (j : Λ) (f : i ⟶ j) (m : ℕ)
      (c : ι → Fin m → A.obj j) (y : Fin m → N.obj j),
      (∀ p, (N.map f).hom (x p) = ∑ q, (φ j) (c p q) • y q) ∧
      (∀ q, ∑ p, (A.map f).hom (a p) * c p q = 0) := by sorry

end RingTheory
