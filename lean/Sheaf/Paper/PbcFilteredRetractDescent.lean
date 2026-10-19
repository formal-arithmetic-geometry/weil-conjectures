/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.FiniteStagePairCategory
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Filtered retract descent for finite PBC coefficient stages

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1541
(blueprint: prop-weil-filtered-retract-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u c
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Every idempotent splits in the actual finite-stage pair category, with its
splitting represented over one finite coefficient field.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1541
(blueprint: prop-weil-filtered-retract-descent).

Proof: choose a representative (M,u) of the idempotent. The generic pair-category
composition and eventual-equality lemmas give P above M where the images of
u composed with u and u agree. Transport conjugates these images by the
associator, so tr_comp and tr_injective show that the transport v is idempotent
on X.toStage h at P. Apply hC P to split v as r followed by i with i followed
by r equal to identity. The transport-class lemma identifies e with [P,r ≫ i].
Include B, i and r into the pair category and conjugate by isoToStage X h.
Functoriality and the inverse equations give the splitting and both displayed
identities. This also constructs the idempotent-completeness instance.
Only the generic StageSystem API underlying the pair definition is needed;
no strict scalar-unit normalization or shift calculus is used.
-/
theorem pbcFilteredRetractDescent
    (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (hC : ∀ E : Padic.FiniteCoefficientFields l Ω,
      IsIdempotentComplete (pbcStageCategory l Ω T E)) :
    IsIdempotentComplete (PbcFiniteStagePairCategory l Ω T hdim hl) ∧
      ∀ (X : PbcFiniteStagePairCategory l Ω T hdim hl) (e : X ⟶ X), e ≫ e = e →
        ∃ (P : Padic.FiniteCoefficientFields l Ω) (h : X.stage ≤ P)
          (B : pbcStageCategory l Ω T P)
          (i : B ⟶ X.toStage h) (r : X.toStage h ⟶ B),
          i ≫ r = 𝟙 B ∧
            e = CategoryTheory.StageSystem.PairCategory.mkHom P h h (r ≫ i) ∧
            ((pbcScalarSystem l Ω T hdim hl).ι P).map i ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).inv ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).hom ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map r =
              𝟙 (((pbcScalarSystem l Ω T hdim hl).ι P).obj B) ∧
            ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).hom ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map r ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map i ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).inv = e := by
  let S := pbcScalarSystem l Ω T hdim hl
  suffices hs : ∀ (X : S.PairCategory) (e : X ⟶ X), e ≫ e = e →
      ∃ (P : Padic.FiniteCoefficientFields l Ω) (h : X.stage ≤ P)
        (B : pbcStageCategory l Ω T P) (i : B ⟶ X.toStage h)
        (r : X.toStage h ⟶ B), i ≫ r = 𝟙 B ∧
          e = StageSystem.PairCategory.mkHom P h h (r ≫ i) by
    constructor
    · refine ⟨fun X e he ↦ ?_⟩
      obtain ⟨P, h, B, i, r, hir, heq⟩ := hs X e he
      refine ⟨(S.ι P).obj B, (S.ι P).map i ≫ (S.isoToStage X h).inv,
        (S.isoToStage X h).hom ≫ (S.ι P).map r, ?_, ?_⟩
      · simp [Category.assoc, ← Functor.map_comp, hir]
      · rw [heq, StageSystem.mkHom_eq_isoToStage]
        simp only [Category.assoc, Functor.map_comp]
    · intro X e he
      obtain ⟨P, h, B, i, r, hir, heq⟩ := hs X e he
      refine ⟨P, h, B, i, r, hir, heq, ?_, ?_⟩
      · simp [← Functor.map_comp, hir]
      · rw [heq, StageSystem.mkHom_eq_isoToStage]
        simp only [Functor.map_comp, Category.assoc]
        rfl
  intro X e he
  obtain ⟨M, _, hX, hX', u, rfl⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq e X.stage
  rw [StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_eq_mkHom_iff] at he
  obtain ⟨P, hMP, hu⟩ := he
  let v : X.toStage (hX.trans hMP) ⟶ X.toStage (hX.trans hMP) := S.tr hMP u
  have hv : v ≫ v = v := by
    rw [← StageSystem.tr_comp]
    exact (StageSystem.tr_injective hMP).mpr hu
  have := hC P
  obtain ⟨B, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split _ v hv
  refine ⟨P, hX.trans hMP, B, i, r, hir, ?_⟩
  rw [hri]
  exact (StageSystem.PairCategory.mkHom_tr hMP u).symm

end AlgebraicGeometry.Scheme
