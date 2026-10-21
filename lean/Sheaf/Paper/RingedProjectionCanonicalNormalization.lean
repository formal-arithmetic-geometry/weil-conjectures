/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Paper.RingedProjectionTensorStructure

/-! # Canonical identity and composition normalization

Source: Stacks Project, Tags 0B56, 06YU, 07A4, 0D6D, 0FPI and 0DV0.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.ProjectionCoherence

private theorem tensor_projection_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (v : U ⋙ G ⟶ (G.prod G) ⋙ V)
    (E : C) (Q : A) :
    (adj.comp adj').homEquiv _ _
        (G.map (t.app (R.obj (S.obj E), Q)) ≫
          v.app (F.obj (R.obj (S.obj E)), F.obj Q) ≫
          V.map (Prod.mkHom ((adj.comp adj').counit.app E) (𝟙 _))) =
      adj.homEquiv _ _ (t.app (R.obj (S.obj E), Q) ≫
          U.map (Prod.mkHom (adj.counit.app (S.obj E)) (𝟙 _))) ≫
        R.map (adj'.homEquiv _ _ (v.app (S.obj E, F.obj Q) ≫
          V.map (Prod.mkHom (adj'.counit.app E) (𝟙 _)))) := by
  apply ((adj.comp adj').homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.comp_homEquiv]
  dsimp only [Equiv.symm_trans_apply]
  erw [adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply,
    adj'.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [G.map_comp]
  have hn := v.naturality (Prod.mkHom (adj.counit.app (S.obj E)) (𝟙 (F.obj Q)))
  dsimp at hn
  slice_rhs 2 3 => rw [hn]
  simp only [Category.assoc]
  rw [← V.map_comp]
  dsimp only [Functor.id_obj]
  congr 2
  congr 1
  ext
  · exact Adjunction.comp_counit_app adj adj' E
  · simp

/-- The composite projection mate is the two successive single-edge mates.
Source: Stacks 0B56 and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
theorem compositeProjection_eq {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z)
    (E : X.mateDerived) (Q : Z.mateDerived) :
    compositeProjection f g a b c E Q =
      g.projection c b (f.right.obj E) Q ≫
        g.right.map (f.projection b a E (g.left.obj Q)) :=
  tensor_projection_comp g.derivedAdjunction f.derivedAdjunction Z.tensor Y.tensor X.tensor
    (g.tensorComparison c b).hom (f.tensorComparison b a).hom E Q

private theorem tensor_projection_conjugate
    {A B : Type*} [Category A] [Category B]
    {F F' : B ⥤ A} {R R' : A ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R')
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : U ⋙ F ⟶ (F.prod F) ⋙ T) (t' : U ⋙ F' ⟶ (F'.prod F') ⋙ T)
    (l : F ≅ F')
    (hl : ∀ P Q : B, l.hom.app (U.obj (P, Q)) ≫ t'.app (P, Q) =
      t.app (P, Q) ≫ T.map (Prod.mkHom (l.hom.app P) (l.hom.app Q)))
    (E : A) (Q : B) :
    adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
        T.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) ≫
      (conjugateIsoEquiv adj adj' l.symm).hom.app (T.obj (E, F.obj Q)) ≫
      R'.map (T.map (Prod.mkHom (𝟙 E) (l.hom.app Q))) =
    U.map (Prod.mkHom ((conjugateIsoEquiv adj adj' l.symm).hom.app E) (𝟙 Q)) ≫
      adj'.homEquiv _ _ (t'.app (R'.obj E, Q) ≫
        T.map (Prod.mkHom (adj'.counit.app E) (𝟙 (F'.obj Q)))) := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [← Category.assoc]
  erw [adj'.homEquiv_naturality_right_symm]
  conv_rhs => erw [adj'.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [adj'.homEquiv_counit, F'.map_comp]
  simp only [Category.assoc]
  dsimp only [conjugateIsoEquiv, Equiv.coe_fn_mk, Iso.symm_hom]
  slice_lhs 2 3 => rw [conjugateEquiv_counit]
  have hn := l.inv.naturality
    (adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
      T.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))))
  dsimp at hn
  dsimp only [Functor.id_obj] at *
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  have hpi : F.map (adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
      T.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))) ≫
      adj.counit.app _ = t.app (R.obj E, Q) ≫
        T.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))) :=
    (adj.homEquiv _ _).symm_apply_apply _
  rw [reassoc_of% hpi]
  have ht := t'.naturality
    (Prod.mkHom ((conjugateEquiv adj adj' l.inv).app E) (𝟙 Q))
  dsimp at ht
  rw [reassoc_of% ht]
  have hi (P Q : B) : l.inv.app (U.obj (P, Q)) ≫ t.app (P, Q) =
      t'.app (P, Q) ≫ T.map (Prod.mkHom (l.inv.app P) (l.inv.app Q)) := by
    apply (cancel_epi (l.hom.app (U.obj (P, Q)))).1
    rw [← Category.assoc, l.hom_inv_id_app, Category.id_comp, reassoc_of% (hl P Q)]
    simp only [← T.map_comp]
    simp
  simp only [← Category.assoc] at *
  rw [hi]
  simp only [Category.assoc, ← T.map_comp]
  congr 2
  ext
  · simp
  · simp


private def compositeTensor
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C}
    {T : A × A ⥤ A} {U : B × B ⥤ B} {V : C × C ⥤ C}
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (v : U ⋙ G ⟶ (G.prod G) ⋙ V) :
    T ⋙ (F ⋙ G) ⟶ ((F ⋙ G).prod (F ⋙ G)) ⋙ V :=
  Functor.whiskerRight t G ≫ Functor.whiskerLeft (F.prod F) v

private def identityTensor {A : Type*} [Category A] (T : A × A ⥤ A) :
    T ⋙ 𝟭 A ⟶ ((𝟭 A).prod (𝟭 A)) ⋙ T where
  app _ := 𝟙 _
  naturality _ _ _ := by simp

set_option maxHeartbeats 800000 in
-- Elaborate the identity and composite ringed tensor interfaces together.
/-- Projection maps respect the normalized identity and composition comparisons.
Source: Stacks 0D6D and 0FPI for pullback comparisons, 0DV0 for their conjugate
counits, and 0B56 for the projection mate.
(blueprint: lem-sfb-ringed-projection-canonical-normalization).

Proof: Construct the derived identity and composition comparisons from the ordinary
module comparisons, on flat-term K-flat representatives. The insertion condition
fixes their scalar-extension maps on generators. These maps preserve tensor products:
both routes insert the same units and associate the same scalars. Descending gives
the normalized comparisons and their tensor equations. Conjugate each pullback
comparison through the derived adjunctions to obtain exactly identityRight and
compositionRight. Transpose the projection squares. Naturality of the tensor
comparison moves the conjugate across it; the conjugate counit equation then
reduces the square to the tensor equation of the pullback comparison. For the
identity adjunction its projection is identity. For composition the composite Hom
equivalence and composite counit formula identify the mate with the two successive
projection mates. This proves both displayed equations without inverting projections. -/
theorem ringedProjectionCanonicalNormalization
    {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z) :
    (∀ (h : RingedTensorEdge X X) (s : Identity h),
        ∃ l : h.left ≅ 𝟭 X.mateDerived, s.Normalized l ∧
          ∀ (E Q : X.mateDerived),
            h.projection a a E Q ≫
                (identityRight h l).hom.app (X.tensor.obj (E, h.left.obj Q)) ≫
                X.tensor.map (Prod.mkHom (𝟙 E) (l.hom.app Q)) =
              X.tensor.map (Prod.mkHom ((identityRight h l).hom.app E) (𝟙 Q))) ∧
    (∀ (h : RingedTensorEdge Z X) (s : Composition f g h),
        ∃ l : h.left ≅ g.left ⋙ f.left, s.Normalized l ∧
          (∀ (E : X.mateDerived) (Q : Z.mateDerived),
            h.projection c a E Q ≫
                (compositionRight f g h l).hom.app (X.tensor.obj (E, h.left.obj Q)) ≫
                g.right.map (f.right.map
                  (X.tensor.map (Prod.mkHom (𝟙 E) (l.hom.app Q)))) =
              Z.tensor.map (Prod.mkHom ((compositionRight f g h l).hom.app E) (𝟙 Q)) ≫
                g.projection c b (f.right.obj E) Q ≫
                g.right.map (f.projection b a E (g.left.obj Q)))) := by
  obtain ⟨t⟩ := ringedProjectionTensorStructure.{u, w}
  constructor
  · intro h s
    obtain ⟨l, hl, ht⟩ := t.identity h a s
    refine ⟨l, hl, ?_⟩
    intro E Q
    have hh := tensor_projection_conjugate h.derivedAdjunction
      (Adjunction.id (C := X.mateDerived)) X.tensor X.tensor
      (h.tensorComparison a a).hom (identityTensor X.tensor) l
      (fun P Q ↦ by simpa [identityTensor] using (ht P Q).symm) E Q
    dsimp only [identityTensor, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.id_obj, Functor.id_map,
      Functor.comp_obj, Functor.comp_map, Adjunction.id_counit, NatTrans.id_app] at hh
    simp only [Adjunction.id_counit, NatTrans.id_app, Category.id_comp,
      ← CategoryTheory.prod_id] at hh
    erw [X.tensor.map_id] at hh
    have hi (D : X.mateDerived) :
        (Adjunction.id (C := X.mateDerived)).homEquiv D D (𝟙 D) = 𝟙 D := by
      calc
        _ = (Adjunction.id (C := X.mateDerived)).unit.app D :=
          (Adjunction.id (C := X.mateDerived)).homEquiv_id D
        _ = 𝟙 D := by rw [Adjunction.id_unit]; rfl
    conv at hh =>
      rhs
      arg 2
      erw [hi]
    rw [Category.comp_id] at hh
    simpa only [RingedTensorEdge.projection, identityRight] using hh
  · intro h s
    obtain ⟨l, hl, ht⟩ := t.composition f g h a b c s
    refine ⟨l, hl, ?_⟩
    intro E Q
    have hh := tensor_projection_conjugate h.derivedAdjunction
      (g.derivedAdjunction.comp f.derivedAdjunction) X.tensor Z.tensor
      (h.tensorComparison c a).hom
      (compositeTensor (g.tensorComparison c b).hom (f.tensorComparison b a).hom) l
      (fun P Q ↦ by simpa [compositeTensor] using ht P Q) E Q
    dsimp only [compositeTensor, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map] at hh
    simp only [Category.assoc] at hh
    change _ = _ ≫ compositeProjection f g a b c E Q at hh
    rw [compositeProjection_eq] at hh
    simpa only [RingedTensorEdge.projection, compositionRight,
      Functor.comp_map, Functor.id_obj, Functor.comp_obj, Category.assoc] using hh

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 800000 in
-- Normalize both composite-adjunction and representative tensor interfaces.
/-- The right-ordered projection composite for a normalized ringed section.
Source: Stacks 0B56, 0D6D, 0FPI and 0DV0.
(blueprint: lem-sfb-ringed-projection-section-specialization). -/
theorem sectionProjectionComparison
    {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
    (a : RingedTensorModel X) (b : RingedTensorModel W) (s : Section i p) :
    ∃ l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived, s.Normalized l ∧
      ∀ V M : X.mateDerived,
        compositeProjection i p a b a V M ≫
            (sectionRight i p l).hom.app (X.tensor.obj (V, i.left.obj (p.left.obj M))) ≫
            X.tensor.map (Prod.mkHom (𝟙 V) (l.hom.app M)) =
          X.tensor.map (Prod.mkHom ((sectionRight i p l).hom.app V) (𝟙 M)) := by
  obtain ⟨t⟩ := ringedProjectionTensorStructure.{u, w}
  obtain ⟨l, hl, ht⟩ := t.sectionComparison i p a b s
  refine ⟨l, hl, ?_⟩
  intro V M
  have hh := tensor_projection_conjugate (p.derivedAdjunction.comp i.derivedAdjunction)
    (Adjunction.id (C := X.mateDerived)) X.tensor X.tensor
    (compositeTensor (p.tensorComparison a b).hom (i.tensorComparison b a).hom)
    (identityTensor X.tensor) l
    (fun P Q ↦ by simpa [compositeTensor, identityTensor] using (ht P Q).symm) V M
  dsimp only [compositeTensor, identityTensor, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.comp_map, Functor.id_obj, Functor.id_map, Adjunction.id_counit,
    NatTrans.id_app] at hh
  simp only [Adjunction.id_counit, NatTrans.id_app, Category.assoc,
    Category.id_comp, ← CategoryTheory.prod_id] at hh
  erw [X.tensor.map_id] at hh
  have hi (D : X.mateDerived) :
      (Adjunction.id (C := X.mateDerived)).homEquiv D D (𝟙 D) = 𝟙 D := by
    calc
      _ = (Adjunction.id (C := X.mateDerived)).unit.app D :=
        (Adjunction.id (C := X.mateDerived)).homEquiv_id D
      _ = 𝟙 D := by rw [Adjunction.id_unit]; rfl
  conv at hh =>
    rhs
    arg 2
    erw [hi]
  rw [Category.comp_id] at hh
  simpa only [sectionRight, compositeProjection, Functor.prod_obj,
    Functor.id_obj, Category.assoc] using hh

end SheafOfModules.ProjectionCoherence
