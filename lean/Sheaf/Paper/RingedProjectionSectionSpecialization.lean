/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Paper.RingedProjectionCanonicalNormalization
import Sheaf.Paper.RingedProjectionTensorStructure

/-! # Section specialization of projection coherence

Source: Stacks Project, Tags 0B56, 06YU, 07A4, 0D6D, 0FPI and 0DV0.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.ProjectionCoherence

/-- The left-ordered projection composite for a specified ringed section is identity.
Source: Stacks 0B56, with the canonical comparisons of 0D6D and 0FPI and the
composite-counit formula of 0DV0.
(blueprint: lem-sfb-ringed-projection-section-specialization).

Proof: Descend the signed associator and symmetry on W to obtain tw with the stated
representative normalization. The specified ordinary section isomorphism descends
to l, normalized on K-flat representatives. On pure tensors its insertion condition
identifies the composite tensor comparison with the identity comparison. The
conjugate sectionRight identifies the composite counit with the identity counit.
First use order V tensor M: transpose the two successive projections through p,
then i. The two counit equations and tensor naturality give the composite projection,
which is identity under l and sectionRight by the preceding normalization. Expand
leftProjection to return to order M tensor V. Naturality moves its inner symmetries
across the projection maps; the adjacent Koszul symmetries cancel. The outside pair
also cancels, since the Koszul sign appears twice. This is sectionComposite = id.
The constraint tx is the canonical one because its normalization on all K-flat
representatives and naturality determine it uniquely; thus the argument applies
to every supplied tx satisfying TensorConstraints. -/
theorem ringedProjectionSectionSpecialization
    {X : RingedTensorCorner.{u, w}} (a : RingedTensorModel X)
    (tx : TensorConstraints X a) :
    (∀ (W : RingedTensorCorner.{u, w}) (i : RingedTensorEdge W X)
          (p : RingedTensorEdge X W) (d : RingedTensorModel W) (s : Section i p),
        ∃ (tw : TensorConstraints W d) (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived),
          s.Normalized l ∧ ∀ M V : X.mateDerived,
            sectionComposite i p a d tx tw l M V = 𝟙 (X.tensor.obj (M, V))) := by
  obtain ⟨t⟩ := ringedProjectionTensorStructure.{u, w}
  intro W i p d s
  obtain ⟨l, hl, hproj⟩ := sectionProjectionComparison i p a d s
  let tw := t.constraints W d
  refine ⟨tw, l, hl, ?_⟩
  intro M V
  have hcancel := tensorConstraints_involutive W d tw (i.right.obj V) (p.left.obj M)
  have hn := tx.symmetry_naturality (𝟙 M) ((sectionRight i p l).inv.app V)
  have hr := (sectionRight i p l).hom.naturality
    (tx.symmetry V (i.left.obj (p.left.obj M))).hom
  have hs := tx.symmetry_naturality (𝟙 V) (l.hom.app M)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hr hs
  have hproj := hproj V M
  rw [compositeProjection_eq] at hproj
  unfold sectionComposite leftProjection
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← p.right.map_comp_assoc, hcancel, p.right.map_id, Category.id_comp]
  rw [reassoc_of% hr]
  rw [← hs]
  simp only [Category.assoc] at hproj ⊢
  rw [reassoc_of% hproj]
  have hc : X.tensor.map (Prod.mkHom ((sectionRight i p l).inv.app V) (𝟙 M)) ≫
      X.tensor.map (Prod.mkHom ((sectionRight i p l).hom.app V) (𝟙 M)) = 𝟙 _ := by
    rw [← X.tensor.map_comp]
    simp
  rw [reassoc_of% hc]
  exact tensorConstraints_involutive X a tx M V

end SheafOfModules.ProjectionCoherence
