/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStage

/-!
# Descent of truncated finite split étale hypercovers to a stage

Starting from `AlgebraicGeometry.HypercoverStageData`, we show that the splitting cofans become
coproducts at a later stage, construct the matching objects at the stage as finite limits of
qcqs étale schemes, show that the matching maps become surjective at a later stage, and assemble
a truncated finite split étale hypercover at that stage whose base change is the given one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} {r : ℕ}
  {U : TruncatedFiniteSplitEtaleHypercover c.pt r}

/-- The index type of the summands of the splitting in degree `Δ`. -/
abbrev SplitIndex {r : ℕ} (Δ : (SimplexCategory.Truncated r)ᵒᵖ) : Type :=
  Σ m : Fin (r + 1), {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}

namespace HypercoverStageData

variable {i : I} (S : HypercoverStageData D c U i)

/-- The legs of the splitting cofan at the stage. -/
def leg (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : SplitIndex Δ) : S.N x.1 ⟶ S.G.obj Δ :=
  S.ι x.1 ≫ S.G.map (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
    (Nat.le_of_lt_succ x.1.isLt)).op

lemma leg_e (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : SplitIndex Δ) :
    (Over.pullback (c.π.app i)).map (S.leg Δ x) ≫ S.e.hom.app Δ =
      (S.a x.1).hom ≫ (Scheme.Etale.forget c.pt).map (U.inclusion x.1 ≫
        U.simplicial.map (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
          (Nat.le_of_lt_succ x.1.isLt)).op) := by
  have nat := S.e.hom.naturality (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
    (Nat.le_of_lt_succ x.1.isLt)).op
  simp only [Functor.comp_map] at nat
  rw [leg, Functor.map_comp, Category.assoc, nat, reassoc_of% (S.hι x.1), Functor.map_comp]
  rfl

/-- The diagram at the stage, as a diagram of qcqs étale schemes. -/
noncomputable def GQ : (SimplexCategory.Truncated r)ᵒᵖ ⥤ qcqsEtale.Over ⊤ (D.obj i) :=
  MorphismProperty.Comma.lift S.G (fun a ↦ (S.hG a).qcqsEtale) (fun _ ↦ trivial)
    (fun _ ↦ trivial)

/-- The `n`-th matching object at the stage. -/
noncomputable def M (n : Fin (r + 1)) : Over (D.obj i) :=
  (MorphismProperty.Over.forget _ _ _).obj (limit (matchingDiagram S.GQ n.val))

lemma isQcqsEtale_M (n : Fin (r + 1)) : IsQcqsEtale (S.M n) :=
  isQcqsEtale_of_qcqsEtale (limit (matchingDiagram S.GQ n.val)).prop

/-- The projections of the `n`-th matching object at the stage. -/
noncomputable def proj (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.M n ⟶ S.G.obj (op Δ) :=
  (MorphismProperty.Over.forget _ _ _).map (limit.π (matchingDiagram S.GQ n.val) (op ⟨Δ, h, θ⟩))

lemma proj_nat (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.proj n Δ h θ ≫ S.G.map α.op = S.proj n Δ' h' (α.hom ≫ θ) := by
  have := limit.w (matchingDiagram S.GQ n.val) (MatchingIndex.homMk h h' α θ).op
  exact congrArg (MorphismProperty.Over.forget _ _ _).map this

/-- The matching object at the stage is a limit. -/
noncomputable def isLimitM (n : Fin (r + 1)) :
    IsLimit (matchingCone S.G n.val (S.M n) (S.proj n) (S.proj_nat n)) :=
  isLimitOfPreserves (MorphismProperty.Over.forget _ _ _)
    (limit.isLimit (matchingDiagram S.GQ n.val))

lemma top_nat (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (_ : Δ.obj.len < n.val) (_ : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.G.map (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op ≫
        S.G.map α.op =
      S.G.map (SimplexCategory.Truncated.Hom.tr (α.hom ≫ θ) Δ'.property
        (Nat.le_of_lt_succ n.isLt)).op := by
  rw [← Functor.map_comp]
  rfl

/-- The `n`-th matching map at the stage. -/
noncomputable def mm (n : Fin (r + 1)) : S.G.obj (op (truncTop n)) ⟶ S.M n :=
  (S.isLimitM n).lift (matchingCone S.G n.val _ (fun Δ _ θ ↦ S.G.map
    (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op) (S.top_nat n))

lemma mm_proj (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.mm n ≫ S.proj n Δ h θ = S.G.map
      (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op :=
  (S.isLimitM n).fac _ (op ⟨Δ, h, θ⟩)

end HypercoverStageData

end AlgebraicGeometry
