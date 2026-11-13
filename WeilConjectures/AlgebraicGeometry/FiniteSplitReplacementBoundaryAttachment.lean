/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementAttachmentStructure

/-! Split simplicial attachment with a prescribed relative matching cover. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Given a finite stage `A`, a boundary `Q`, and a surjection `b : N ⟶ Q.M` from a finite
coproduct of qcqs étale pieces compatible with a map `g` to `K`, there is a finite replacement
stage of degree `n + 1` restricting to `A` (Stacks, Tags 0DAV, 01GJ). -/
theorem exists_replacement_stage_of_boundary_cover
    {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    {n : ℕ} (A : FiniteSplitReplacementStage K n) (Q : ReplacementBoundary A.U)
    (N : X.Etale) (b : N ⟶ Q.M)
    (g : N ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hc : Surjective b.left)
    (hf : ∃ (k : ℕ) (V : Fin k → X.Etale) (ι : ∀ i, V i ⟶ N),
      Nonempty (IsColimit (Cofan.mk N ι)) ∧
        ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
          LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
            QuasiSeparated (V i).hom)
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op) :
    ∃ B : FiniteSplitReplacementStage K (n + 1), B.restrict n (Nat.le_succ n) = A := by
  classical
  obtain ⟨U, hU, hr⟩ := SchemeSplitAttachment.exists_attached_split_structure
    A.U N Q b hc hf
  let B : FiniteSplitReplacementStage K (n + 1) :=
    ⟨U, eqToHom hU ≫ SchemeSplitAttachment.attachedRefinement A N Q b g hcomp⟩
  refine ⟨B, ?_⟩
  have stage_ext {A B : FiniteSplitReplacementStage K n} (h : A.U = B.U)
      (hf : A.f = eqToHom (congrArg TruncatedFiniteSplitEtaleHypercover.simplicial h) ≫
        B.f) : A = B := by
    cases A with
    | mk AU Af =>
      cases B with
      | mk BU Bf =>
        cases h
        simp only [eqToHom_refl, Category.id_comp] at hf
        cases hf
        rfl
  apply stage_ext hr
  change (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).map
    (eqToHom hU ≫ SchemeSplitAttachment.attachedRefinement A N Q b g hcomp) = _
  rw [Functor.map_comp, eqToHom_map,
    SchemeSplitAttachment.attachedRefinement_restrict]
  simp only [eqToHom_trans_assoc]

end AlgebraicGeometry
