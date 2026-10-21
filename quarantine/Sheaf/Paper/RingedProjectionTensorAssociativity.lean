/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Paper.RingedProjectionTensorStructure

/-! # Tensor associativity for projection mates

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

private theorem tensor_projection_associativity
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U)
    (aa : ∀ E Q N : B, U.obj (U.obj (E, Q), N) ≅ U.obj (E, U.obj (Q, N)))
    (bb : ∀ E Q N : A, T.obj (T.obj (E, Q), N) ≅ T.obj (E, T.obj (Q, N)))
    (ha : ∀ {E E' Q Q' N N'} (x : E ⟶ E') (y : Q ⟶ Q') (z : N ⟶ N'),
      U.map (Prod.mkHom (U.map (Prod.mkHom x y)) z) ≫ (aa E' Q' N').hom =
        (aa E Q N).hom ≫ U.map (Prod.mkHom x (U.map (Prod.mkHom y z))))
    (ht : ∀ E Q N,
      F.map (bb E Q N).inv ≫ t.app (T.obj (E, Q), N) ≫
          U.map (Prod.mkHom (t.app (E, Q)) (𝟙 (F.obj N))) =
        t.app (E, T.obj (Q, N)) ≫
          U.map (Prod.mkHom (𝟙 (F.obj E)) (t.app (Q, N))) ≫
          (aa (F.obj E) (F.obj Q) (F.obj N)).inv)
    (E : B) (Q N : A) :
    adj.homEquiv _ _ (t.app (R.obj E, T.obj (Q, N)) ≫
        U.map (Prod.mkHom (adj.counit.app E) (𝟙 _))) ≫
      R.map (U.map (Prod.mkHom (𝟙 E) (t.app (Q, N)))) ≫
      R.map (aa E (F.obj Q) (F.obj N)).inv =
    (bb (R.obj E) Q N).inv ≫
      T.map (Prod.mkHom
        (adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
          U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)))) (𝟙 N)) ≫
      adj.homEquiv _ _ (t.app (R.obj (U.obj (E, F.obj Q)), N) ≫
        U.map (Prod.mkHom (adj.counit.app _) (𝟙 _))) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [← R.map_comp, adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
  conv_rhs =>
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_left_symm]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
  let p := adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
    U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  have hn := t.naturality (Prod.mkHom p (𝟙 N))
  dsimp at hn
  have he : F.map p ≫ adj.counit.app _ =
      t.app (R.obj E, Q) ≫ U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)) :=
    (adj.homEquiv _ _).symm_apply_apply _
  change _ = F.map (bb (R.obj E) Q N).inv ≫
    F.map (T.map (Prod.mkHom p (𝟙 N))) ≫ t.app (_, N) ≫
    U.map (Prod.mkHom (adj.counit.app _) (𝟙 _))
  dsimp only [Functor.id_obj] at *
  rw [Category.assoc, ← Category.assoc (F.map (T.map _)), hn]
  simp only [Category.assoc, ← U.map_comp]
  have hm : Prod.mkHom (F.map p) (F.map (𝟙 N)) ≫
      Prod.mkHom (adj.counit.app (U.obj (E, F.obj Q))) (𝟙 (F.obj N)) =
      Prod.mkHom (t.app (R.obj E, Q) ≫
        U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) (𝟙 (F.obj N)) := by
    ext <;> simp [he]
  rw [hm]
  have hc : U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj (T.obj (Q, N))))) ≫
      U.map (Prod.mkHom (𝟙 E) (t.app (Q, N))) =
      U.map (Prod.mkHom (𝟙 (F.obj (R.obj E))) (t.app (Q, N))) ≫
        U.map (Prod.mkHom (adj.counit.app E) (𝟙 (U.obj (F.obj Q, F.obj N)))) := by
    simp only [← U.map_comp]
    congr 1
    ext <;> simp
  rw [← Category.assoc (U.map _), hc, Category.assoc]
  have hai : U.map (Prod.mkHom (adj.counit.app E) (𝟙 (U.obj (F.obj Q, F.obj N)))) ≫
      (aa E (F.obj Q) (F.obj N)).inv =
      (aa (F.obj (R.obj E)) (F.obj Q) (F.obj N)).inv ≫
        U.map (Prod.mkHom
          (U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) (𝟙 (F.obj N))) := by
    apply (cancel_epi (aa (F.obj (R.obj E)) (F.obj Q) (F.obj N)).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hh := ha (adj.counit.app E) (𝟙 (F.obj Q)) (𝟙 (F.obj N))
    simpa using congrArg (fun v ↦ v ≫ (aa E (F.obj Q) (F.obj N)).inv) hh.symm
  rw [hai]
  simp only [← Category.assoc]
  have ht' := ht (R.obj E) Q N
  simp only [← Category.assoc] at ht'
  rw [← ht']
  simp only [Category.assoc, ← U.map_comp]
  congr 3
  ext <;> simp

/-- Canonical constraints and tensor associativity for a single ringed-topos projection.
Source: Stacks 06YU and 07A4 for the signed derived constraints; 0B56 for the mate.
(blueprint: lem-sfb-ringed-projection-tensor-associativity).

Proof: Descend the signed total-complex associator and Koszul symmetry along the
flat-term K-flat localization. Naturality and the representative normalization give
TensorConstraints on each corner. On triple pure tensors pullback inserts the same
units along both associator paths, so its canonical tensor comparison is associative.
Transpose the displayed equality through f.left ⊣ f.right. On the two-projection
path, apply the counit equation for the second projection, move the first projection
through the tensor comparison by naturality, then apply its counit equation.
The result is the tensor of the counit with two identity maps, preceded by the two
tensor comparisons. Their associativity equation identifies this with the transpose
of the single-projection path. Injectivity of the Hom equivalence gives the equality.
No boundedness or invertibility of a projection is needed. -/
theorem ringedProjectionTensorAssociativity
    {X Y : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) :
    ∃ (tx : TensorConstraints X a) (ty : TensorConstraints Y b),
      (∀ (E : X.mateDerived) (Q T : Y.mateDerived),
        f.projection b a E (Y.tensor.obj (Q, T)) ≫
            f.right.map (X.tensor.map
              (Prod.mkHom (𝟙 E) ((f.tensorComparison b a).hom.app (Q, T)))) ≫
            f.right.map (tx.associator E (f.left.obj Q) (f.left.obj T)).inv =
          (ty.associator (f.right.obj E) Q T).inv ≫
            Y.tensor.map (Prod.mkHom (f.projection b a E Q) (𝟙 T)) ≫
            f.projection b a (X.tensor.obj (E, f.left.obj Q)) T) := by
  obtain ⟨s⟩ := ringedProjectionTensorStructure.{u, w}
  refine ⟨s.constraints X a, s.constraints Y b, ?_⟩
  intro E Q T
  exact tensor_projection_associativity f.derivedAdjunction Y.tensor X.tensor
    (f.tensorComparison b a).hom (s.constraints X a).associator
    (s.constraints Y b).associator (s.constraints X a).associator_naturality
    (s.associativity f a b) E Q T

end SheafOfModules.ProjectionCoherence
