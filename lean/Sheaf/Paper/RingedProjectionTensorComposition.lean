/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q48 and V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Paper.RingedProjectionTensorAssociativity
import Sheaf.Paper.RingedProjectionCanonicalNormalization
import Sheaf.Paper.RingedProjectionSectionSpecialization

/-! # Tensor and composition coherence of ringed-topos projection maps

Source: Stacks Project, Tags 0B56 and 0DV0.
(blueprint: lem-sfb-ringed-projection-tensor-composition).
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

private theorem tensor_projection_naturality
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U)
    {E E' : B} {Q Q' : A} (v : E ⟶ E') (z : Q ⟶ Q') :
    T.map (CategoryTheory.Prod.mkHom (R.map v) z) ≫
        adj.homEquiv _ _ (t.app (R.obj E', Q') ≫
          U.map (CategoryTheory.Prod.mkHom (adj.counit.app E') (𝟙 (F.obj Q')))) =
      adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
          U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) ≫
        R.map (U.map (CategoryTheory.Prod.mkHom v (F.map z))) := by
  apply adj.homEquiv_naturality_left_square
  have hn := t.naturality (CategoryTheory.Prod.mkHom (R.map v) z)
  dsimp at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext
  · exact adj.counit.naturality v
  · simp

private theorem projection_naturality
    {X Y : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y)
    {E E' : X.mateDerived} {Q Q' : Y.mateDerived} (v : E ⟶ E') (z : Q ⟶ Q') :
    Y.tensor.map (Prod.mkHom (f.right.map v) z) ≫ f.projection b a E' Q' =
      f.projection b a E Q ≫
        f.right.map (X.tensor.map (Prod.mkHom v (f.left.map z))) :=
  tensor_projection_naturality f.derivedAdjunction Y.tensor X.tensor
    (f.tensorComparison b a).hom v z

set_option maxHeartbeats 800000 in
-- Elaborating the nine coherence clauses repeats the ringed-module tensor interfaces.
/-- All projection coherence identities for arbitrary unbounded ringed-topos modules.
Source: Stacks 0B56 (`equation-projection-formula-map`) and Categories 0DV0
(`lemma-compose-counits`), including formal tensor associativity and section specialization
(blueprint: lem-sfb-ringed-projection-tensor-composition).

Proof:
1. By lem-sfb-ringed-projection-tensor-structure, the representative-defined tensor
constraints commute with pullback; pullback composition is monoidal and the direct-image
comparison is its adjunction conjugate. For any h, transpose the projection using
lem-weil-pbc-adjunct-counit-identity: its transpose is tensor comparison followed by
counit tensor identity. This characterizes the projection uniquely, without bounds.
2. Transpose the two naturality paths. Naturality of the tensor comparison and counit
makes their transposes equal. For the identity adjunction, the transpose is the identity.
3. For the tensor identity, transpose the two successive projections. Apply the defining
counit equation twice and tensor-comparison naturality. Associativity coherence identifies
the resulting tensor of the counit with the transpose of the single projection for Q⊗T.
The explicit associators below put both maps in the same source and target.
4. For composition, transpose first through g, then through f. The composite Hom bijection
of def-weil-pbc-composite-adjunction is injective. The composite counit formula in Tag
0DV0 identifies the result with the transpose of compositeProjection.
5. For a section, use its representative-normalized pullback comparison and the conjugate
right comparison. The composition identity becomes the identity projection. Conjugate by
tensor symmetry to obtain sectionComposite: the two interior symmetries cancel, and the
outside symmetries compose to identity. No projection arrow is inverted.
-/
theorem ringedProjectionTensorComposition
    {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z) :
    ∃ (tx : TensorConstraints X a) (ty : TensorConstraints Y b),
      (∀ (E E' : X.mateDerived) (Q Q' : Y.mateDerived) (v : E ⟶ E') (z : Q ⟶ Q'),
        Y.tensor.map (Prod.mkHom (f.right.map v) z) ≫ f.projection b a E' Q' =
          f.projection b a E Q ≫
            f.right.map (X.tensor.map (Prod.mkHom v (f.left.map z)))) ∧
      (∀ (E E' : Y.mateDerived) (Q Q' : Z.mateDerived) (v : E ⟶ E') (z : Q ⟶ Q'),
        Z.tensor.map (Prod.mkHom (g.right.map v) z) ≫ g.projection c b E' Q' =
          g.projection c b E Q ≫
            g.right.map (Y.tensor.map (Prod.mkHom v (g.left.map z)))) ∧
      (∀ (E E' : X.mateDerived) (Q Q' : Z.mateDerived) (v : E ⟶ E') (z : Q ⟶ Q'),
        Z.tensor.map (Prod.mkHom (g.right.map (f.right.map v)) z) ≫
            compositeProjection f g a b c E' Q' =
          compositeProjection f g a b c E Q ≫
            g.right.map (f.right.map
              (X.tensor.map (Prod.mkHom v (f.left.map (g.left.map z)))))) ∧
      (∀ (E Q : X.mateDerived), identityProjection X E Q = 𝟙 (X.tensor.obj (E, Q))) ∧
      (∀ (h : RingedTensorEdge X X) (s : Identity h),
        ∃ l : h.left ≅ 𝟭 X.mateDerived, s.Normalized l ∧
          ∀ (E Q : X.mateDerived),
            h.projection a a E Q ≫
                (identityRight h l).hom.app (X.tensor.obj (E, h.left.obj Q)) ≫
                X.tensor.map (Prod.mkHom (𝟙 E) (l.hom.app Q)) =
              X.tensor.map (Prod.mkHom ((identityRight h l).hom.app E) (𝟙 Q))) ∧
      (∀ (E : X.mateDerived) (Q T : Y.mateDerived),
        f.projection b a E (Y.tensor.obj (Q, T)) ≫
            f.right.map (X.tensor.map
              (Prod.mkHom (𝟙 E) ((f.tensorComparison b a).hom.app (Q, T)))) ≫
            f.right.map (tx.associator E (f.left.obj Q) (f.left.obj T)).inv =
          (ty.associator (f.right.obj E) Q T).inv ≫
            Y.tensor.map (Prod.mkHom (f.projection b a E Q) (𝟙 T)) ≫
            f.projection b a (X.tensor.obj (E, f.left.obj Q)) T) ∧
      (∀ (E : X.mateDerived) (Q : Z.mateDerived),
        compositeProjection f g a b c E Q =
          g.projection c b (f.right.obj E) Q ≫
            g.right.map (f.projection b a E (g.left.obj Q))) ∧
      (∀ (h : RingedTensorEdge Z X) (s : Composition f g h),
        ∃ l : h.left ≅ g.left ⋙ f.left, s.Normalized l ∧
          (∀ (E E' : X.mateDerived) (Q Q' : Z.mateDerived) (v : E ⟶ E') (z : Q ⟶ Q'),
            Z.tensor.map (Prod.mkHom (h.right.map v) z) ≫ h.projection c a E' Q' =
              h.projection c a E Q ≫
                h.right.map (X.tensor.map (Prod.mkHom v (h.left.map z)))) ∧
          (∀ (E : X.mateDerived) (Q : Z.mateDerived),
            h.projection c a E Q ≫
                (compositionRight f g h l).hom.app (X.tensor.obj (E, h.left.obj Q)) ≫
                g.right.map (f.right.map
                  (X.tensor.map (Prod.mkHom (𝟙 E) (l.hom.app Q)))) =
              Z.tensor.map (Prod.mkHom ((compositionRight f g h l).hom.app E) (𝟙 Q)) ≫
                g.projection c b (f.right.obj E) Q ≫
                g.right.map (f.projection b a E (g.left.obj Q)))) ∧
      (∀ (W : RingedTensorCorner.{u, w}) (i : RingedTensorEdge W X)
          (p : RingedTensorEdge X W) (d : RingedTensorModel W) (s : Section i p),
        ∃ (tw : TensorConstraints W d) (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived),
          s.Normalized l ∧ ∀ M V : X.mateDerived,
            sectionComposite i p a d tx tw l M V = 𝟙 (X.tensor.obj (M, V))) := by
  obtain ⟨tx, ty, htensor⟩ := ringedProjectionTensorAssociativity f a b
  obtain ⟨hid, hcomp⟩ := ringedProjectionCanonicalNormalization f g a b c
  refine ⟨tx, ty, ?_, ?_, ?_, ?_, hid, htensor, ?_, ?_, ?_⟩
  · intro E E' Q Q' v z
    exact projection_naturality f a b v z
  · intro E E' Q Q' v z
    exact projection_naturality g b c v z
  · intro E E' Q Q' v z
    rw [compositeProjection_eq, compositeProjection_eq]
    rw [← Category.assoc, projection_naturality g b c (f.right.map v) z,
      Category.assoc, ← g.right.map_comp]
    rw [projection_naturality f a b v (g.left.map z)]
    rw [g.right.map_comp]
    simp only [Category.assoc]
  · intro E Q
    rw [identityProjection, Adjunction.homEquiv_unit]
    simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_map]
    exact Category.id_comp _
  · exact compositeProjection_eq f g a b c
  · intro h s
    obtain ⟨l, hl, heq⟩ := hcomp h s
    refine ⟨l, hl, ?_, heq⟩
    intro E E' Q Q' v z
    exact projection_naturality h a c v z
  · exact ringedProjectionSectionSpecialization a tx

end SheafOfModules.ProjectionCoherence
