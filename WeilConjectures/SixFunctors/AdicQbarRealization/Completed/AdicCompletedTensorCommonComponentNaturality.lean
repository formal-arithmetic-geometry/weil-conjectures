/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorStageNaturality
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorComponentStageTransport

/-! # Naturality of the explicit completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

private theorem conjugated_square {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) {P Q P' Q' : C} (a : P ≅ P') (b : Q ≅ Q')
    (s : F.obj P' ⟶ G.obj P') (t : F.obj Q' ⟶ G.obj Q') (f : P' ⟶ Q')
    (h : F.map f ≫ t = s ≫ G.map f) :
    F.map (a.hom ≫ f ≫ b.inv) ≫ (F.map b.hom ≫ t ≫ G.map b.inv) =
      (F.map a.hom ≫ s ≫ G.map a.inv) ≫ G.map (a.hom ≫ f ≫ b.inv) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc b.inv b.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← G.map_comp_assoc a.inv a.hom, Iso.inv_hom_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ F.map a.hom ≫ k ≫ G.map b.inv) h

/-- Naturality of the explicitly constructed common-field tensor comparison.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-component-naturality).

Proof: represent the two coordinates of the input arrow by rational arrows over
finite fields and enlarge both representatives to a common upper field E. The
exists_mkHom_eq and mkHom_eq_isoToStage equations express the original arrow as
the included rational pair conjugated by the actual endpoint isoToStage maps.
Apply completedTensorCommonComponent_stage_transport to both endpoints: its
coefficient-enlargement equation expresses each component as the finite-stage
component conjugated by those same endpoint maps. At E, apply
completedTensorStageComponent_naturality to the rational pair. The private
conjugated_square lemma uses functoriality and the inverse identities of the
endpoint isomorphisms to turn this finite square into the required square.
These arguments also cover zero objects and arrows, coincident stages, and an
empty scheme. -/
theorem completedTensorCommonComponent_naturality
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    {P Q : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ×
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X}
    (f : P ⟶ Q) :
    (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map f ≫
        (completedTensorCommonComponent l X R closed models N Q.1 Q.2).hom =
      (completedTensorCommonComponent l X R closed models N P.1 P.2).hom ≫
        (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map f := by
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X
  let F := ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
  let G := commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  obtain ⟨E₁, hP₁, hQ₁, ha⟩ := StageSystem.PairCategory.exists_mkHom_eq f.1
  obtain ⟨E₂, hP₂, hQ₂, hb⟩ := StageSystem.PairCategory.exists_mkHom_eq f.2
  obtain ⟨E, h₁, h₂⟩ := exists_ge_ge E₁ E₂
  obtain ⟨a, ha⟩ := ha E h₁
  obtain ⟨b, hb⟩ := hb E h₂
  let eP := Iso.prod (S.isoToStage P.1 (hP₁.trans h₁))
    (S.isoToStage P.2 (hP₂.trans h₂))
  let eQ := Iso.prod (S.isoToStage Q.1 (hQ₁.trans h₁))
    (S.isoToStage Q.2 (hQ₂.trans h₂))
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  have hf : f = eP.hom ≫ (I.prod I).map (Prod.mkHom a b) ≫ eQ.inv := by
    apply Prod.ext
    · exact ha.trans (StageSystem.mkHom_eq_isoToStage _ _ a)
    · exact hb.trans (StageSystem.mkHom_eq_isoToStage _ _ b)
  change F.map f ≫ _ = _ ≫ G.map f
  rw [completedTensorCommonComponent_stage_transport l X R closed models symmetry N coherence
      Q.1 Q.2 E (hQ₁.trans h₁) (hQ₂.trans h₂),
    completedTensorCommonComponent_stage_transport l X R closed models symmetry N coherence
      P.1 P.2 E (hP₁.trans h₁) (hP₂.trans h₂)]
  rw [hf]
  exact conjugated_square F G eP eQ _ _ _
    (completedTensorStageComponent_naturality l X R closed models E (N E)
      (Prod.mkHom a b))

end WeilConjectures.AdicQbarRealization
