/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # EtaleSingletonTensorCechCofaceEvaluation

## References

* Stacks Project, Tags 03P2 and 03DR
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

-- Avoid expanding tensor pullback constructions during proof elaboration.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
  Modules.etaleTensorSectionsRestriction

private theorem uliftMap_down {A B : AddCommGrpCat.{u}} (f : A ⟶ B)
    (t : ULift.{u + 1} A) :
    (AddCommGrpCat.uliftFunctor.map f t).down = f t.down := by
  rfl

private theorem tensorMap_eq
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) {P Q : Over U} (f : P ⟶ Q) :
    let G := (Over.forget U).op ⋙
      (((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)
    G.map f.op = AddCommGrpCat.uliftFunctor.map
      (Modules.etaleTensorSectionsRestriction F f.left) := by
  rfl

-- Share the caller's smallness witness so specialization preserves the chosen product.
private theorem liftedTensorMap_projection_down
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) (P Q : Over U) (I : Type) [Small.{u + 1} I] (i : I) :
    let G := (Over.forget U).op ⋙
      (((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)
    ∀ (a : G.obj (op Q) ⟶ G.obj (op P))
      (r : Γ((Modules.tensorPullback Q.left.hom).obj F, ⊤) ⟶
        Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))
      (s : (piObj (fun _ : I ↦ G.obj (op Q)) : AddCommGrpCat.{u + 1})),
    a = AddCommGrpCat.uliftFunctor.map r →
    (a (Pi.π (fun _ : I ↦ G.obj (op Q)) i s)).down =
      r ((Pi.π (fun _ : I ↦ AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback Q.left.hom).obj F, ⊤))) i s).down) := by
  intro G a r s ha
  subst a
  have hπ : Pi.π (fun _ : I ↦ G.obj (op Q)) i =
      Pi.π (fun _ : I ↦ AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback Q.left.hom).obj F, ⊤))) i := rfl
  rw [hπ]
  exact uliftMap_down r _

private theorem singletonCoface_projection (X : Scheme.{u}) (U : X.Etale)
    (V : Over U) (G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (n : ℕ) (j : Fin (n + 2))
    (s : ((cechComplexFunctor (fun _ : Fin 1 ↦ V)).obj G).X n) :
    Pi.π (fun _ : Fin (n + 2) → Fin 1 ↦
      G.obj (op (∏ᶜ (fun _ : Fin (n + 2) ↦ V)))) (fun _ ↦ 0)
      (((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ (fun _ : Fin 1 ↦ V)).cech).obj G).δ j s) =
    G.map (Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ V) (j.succAbove k))).op
      (Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
        G.obj (op (∏ᶜ (fun _ : Fin (n + 1) ↦ V)))) (fun _ ↦ 0) s) := by
  dsimp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  erw [Pi.lift_comp_π_apply]
  rfl

/-- Raw categorical coface projection, before evaluating lifted sections. -/
theorem singletonTensorCech_coface_raw_projection
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (s : (singletonTensorCech X F U W g).X n) :
    let G := (Over.forget U).op ⋙
      (((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)
    let P := ∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)
    let Q := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    let f := Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k))
    Pi.π (fun _ : Fin (n + 2) → Fin 1 ↦ G.obj (op P)) (fun _ ↦ 0)
        ((singletonTensorCechCosimplicial X F U W g).δ j s) =
      G.map f.op (Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ G.obj (op Q)) (fun _ ↦ 0) s) := by
  intro G P Q f
  exact singletonCoface_projection X U (Over.mk g) G n j s

-- Keep the unused `P` let-binding in the existing public statement.
set_option linter.unusedVariables false in
/-- Downstairs evaluation of the raw coface map is restriction (Stacks, Tags 03P2 and 03DR). -/
theorem singletonTensorCech_coface_map_down
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (s : (singletonTensorCech X F U W g).X n) :
    let G := (Over.forget U).op ⋙
      (((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)
    let P := ∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)
    let Q := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    let f := Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k))
    (G.map f.op (Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ G.obj (op Q)) (fun _ ↦ 0) s)).down =
      Modules.etaleTensorSectionsRestriction F f.left
        ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
          AddCommGrpCat.of (ULift.{u + 1}
            Γ((Modules.tensorPullback Q.left.hom).obj F, ⊤))) (fun _ ↦ 0) s).down)  := by
  intro G P Q f
  exact liftedTensorMap_projection_down X F U P Q (Fin (n + 1) → Fin 1) (fun _ ↦ 0)
    (G.map f.op) (Modules.etaleTensorSectionsRestriction F f.left) s (tensorMap_eq X F U f)


/-- Evaluation of a singleton Čech coface is restriction along the product map
(Stacks, Tags 03P2 and 03DR). -/
theorem singletonTensorCech_coface_evaluation
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (s : (singletonTensorCech X F U W g).X n) :
    ((Pi.π (fun _ : Fin (n + 2) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) ((singletonTensorCechCosimplicial X F U W g).δ j s)).down =
    Modules.etaleTensorSectionsRestriction F (Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k))).left
      (((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) s).down) := by
  have h := singletonTensorCech_coface_raw_projection X F U W g n j s
  have h' := singletonTensorCech_coface_map_down X F U W g n j s
  exact (congrArg ULift.down h).trans h'

end
end AlgebraicGeometry.Scheme
