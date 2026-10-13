/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

/- helper construction -/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
abbrev etaleSetInverseImageConstantSheafHom (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :=
  (Scheme.etaleSetPullback v).obj
            ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
              (ULift.{u + 1, u} E)) ⟶
          (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
            (ULift.{u + 1, u} E)

def etaleSetInverseImageConstantSheafCondition
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u)
    (γ : etaleSetInverseImageConstantSheafHom U V v E) : Prop :=
  (∀ e : E,
        γ.hom.app (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
          (Scheme.Etale.mk (𝟙 U))))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback
            (P := @AlgebraicGeometry.Etale) (Q := ⊤) v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
                (ULift.{u + 1, u} E))).hom.app
            (Opposite.op (Scheme.Etale.mk (𝟙 U)))
            (((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                (Opposite.op (Scheme.Etale.mk (𝟙 U))) ⟨e⟩))) =
          (toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
            (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
              (Scheme.Etale.mk (𝟙 U)))) ⟨e⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Construction of the canonical isomorphism and its section equations.
(blueprint: new-etaleSetInverseImageConstantSheaf-existence) -/
theorem etaleSetInverseImageConstantSheaf_exists
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :
    ∃ γ : etaleSetInverseImageConstantSheafHom U V v E,
      etaleSetInverseImageConstantSheafCondition U V v E γ ∧ IsIso γ := by
  let T := Scheme.Etale.mk (𝟙 U)
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun W ↦ MorphismProperty.Over.homMk W.hom) (fun W f ↦ by
      apply MorphismProperty.Over.Hom.ext
      change f.left = W.hom
      rw [← MorphismProperty.Over.w f]
      exact (Category.comp_id _).symm)
  let hBT : IsTerminal
      ((MorphismProperty.Over.pullback @Etale ⊤ v).obj T) :=
    hT.isTerminalObj (MorphismProperty.Over.pullback @Etale ⊤ v) T
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
    (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale)
  let a₁ := ((constantSheafAdj U.smallEtaleTopology (Type (u + 1)) hT).comp a).ofNatIsoRight
    (Functor.sheafPushforwardContinuousCompSheafSectionsObjIso
      (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
      (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale) (op T))
  let a₂ := constantSheafAdj V.smallEtaleTopology (Type (u + 1)) hBT
  let i := a₁.leftAdjointUniq a₂
  refine ⟨i.hom.app (ULift.{u + 1, u} E), ?_, inferInstance⟩
  intro e
  have h := a₁.unit_leftAdjointUniq_hom_app a₂ (ULift.{u + 1, u} E)
  have he := congrArg (fun f ↦ f (ULift.up e)) h
  convert he using 1 <;> simp [a₁, a₂, a, i, T, constantSheafAdj, constantPresheafAdj,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso] <;> rfl
end AlgebraicGeometry
