/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ChowFiniteType
import WeilConjectures.AlgebraicGeometry.ClosedChowStage
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap

/-!
# Properness descends to a finite stage

Source: Stacks Project, Limits, Lemma 081F in Situation 081D.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A locally finite type morphism between qcqs schemes over a qcqs stage of an inverse
system with affine transitions is proper at some later stage if its base change to the
limit is proper. The distinguished index `i₀` need not be a least element.

Source: Stacks Project, Limits, Lemma 081F in Situation 081D. -/
theorem exists_isProper_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (a : X₀ ⟶ D.obj (op i₀)) (b : Y₀ ⟶ D.obj (op i₀))
    (f₀ : X₀ ⟶ Y₀) (h : f₀ ≫ b = a) [LocallyOfFiniteType f₀]
    (hf : IsProper (pullback.map a (c.π.app (op i₀)) b (c.π.app (op i₀))
      f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
      ((Category.comp_id a).trans h.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsProper (pullback.map a (D.map (homOfLE hi).op) b (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        ((Category.comp_id a).trans h.symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  let X : Over (D.obj (op i₀)) := Over.mk a
  let Y : Over (D.obj (op i₀)) := Over.mk b
  let f : X ⟶ Y := Over.homMk f₀ h
  have : CompactSpace X.left := inferInstanceAs (CompactSpace X₀)
  have : QuasiSeparatedSpace X.left := inferInstanceAs (QuasiSeparatedSpace X₀)
  have : CompactSpace Y.left := inferInstanceAs (CompactSpace Y₀)
  have : QuasiSeparatedSpace Y.left := inferInstanceAs (QuasiSeparatedSpace Y₀)
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType f₀)
  have hf' : IsProper (((Over.pullback (c.π.app (op i₀))).map f).left) := by
    simpa [X, Y, f, Over.pullback, pullback.map] using hf
  have hsep : IsSeparated (((Over.pullback (c.π.app (op i₀))).map f).left) :=
    hf'.toIsSeparated
  obtain ⟨i₁, h₁, hsep₁⟩ := Scheme.exists_isSeparated_overPullbackMap D c hc i₀ X Y f hsep
  let B := Over.pullback (D.map (homOfLE h₁).op)
  have : IsSeparated (B.map f).left := hsep₁
  have : LocallyOfFiniteType (B.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have : CompactSpace (B.obj Y).left := by dsimp [B, Y, Over.pullback]; infer_instance
  have : QuasiSeparatedSpace (B.obj Y).left := by
    dsimp [B, Y, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace (B.obj X).left := by dsimp [B, X, Over.pullback]; infer_instance
  obtain ⟨n, T₁, π₁, j₁, hπ₁, hsurj₁, hj₁, hw₁⟩ := exists_chow_finite_type (B.map f).left
  obtain ⟨i, h₁i, π, j, hsurj, hj, hw, hsepᵢ⟩ :=
    exists_closed_chow_stage D c hc i₀ X Y f hf' i₁ h₁ hsep₁
      n T₁ π₁ j₁ hπ₁ hsurj₁ hj₁ hw₁
  let Bi := Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)
  have : Surjective π := hsurj
  have : IsClosedImmersion j := hj
  have : IsProper (π ≫ (Bi.map f).left) := by
    rw [← hw]
    infer_instance
  have : IsSeparated (Bi.map f).left := hsepᵢ
  have : LocallyOfFiniteType (Bi.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have hp : IsProper (Bi.map f).left := by
    rw [isProper_iff]
    exact ⟨inferInstance, UniversallyClosed.of_comp_surjective π _, inferInstance⟩
  refine ⟨i, h₁.trans h₁i, ?_⟩
  simpa [Bi, X, Y, f, Over.pullback, pullback.map] using hp

end AlgebraicGeometry
