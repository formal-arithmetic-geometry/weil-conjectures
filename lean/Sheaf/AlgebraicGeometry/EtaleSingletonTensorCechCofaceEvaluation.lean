/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # EtaleSingletonTensorCechCofaceEvaluation
Source: Stacks Project, Tags 03P2 and 03DR.
(blueprint: lem-sc-singleton-tensor-cech-coface-evaluation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Raw categorical coface projection, before evaluating lifted sections.
(blueprint: new-etale-singleton-tensor-cech-coface-raw-projection)
Proof: unfold the formal coproduct coface and apply the product projection equation. -/
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
  sorry

/-- Downstairs evaluation of the raw coface map is restriction.
(blueprint: new-etale-singleton-tensor-cech-coface-map-down)
Proof: apply the lifted tensor section restriction evaluation and remove ULift. -/
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
  sorry


/-- Evaluation of a singleton Čech coface is restriction along the product map.
Source: Stacks Project, Tag 03P2 (Čech restriction formula), Tag 03DR.
(blueprint: lem-sc-singleton-tensor-cech-coface-evaluation)

Proof: unfold the formal-coproduct Čech face. Its index map sends a tuple t
of length n+2 to t composed with j.succAbove. Its component is Pi.lift of
the retained product projections. The extension of a presheaf to formal
coproducts sends this face to Pi.lift of the source projection followed by
restriction along that component. Composing with the projection at the
constant-zero tuple and applying Pi.lift_π selects that restriction. The
source tuple is again constant zero. The lifted tensor-section presheaf
maps the component by ULift of etaleTensorSectionsRestriction, so taking
down gives the displayed equation. This is a statement about every section,
not about comparison maps or tensors. For n=0 it gives the two projection
restrictions; on zero section groups both sides are zero.
-/
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
