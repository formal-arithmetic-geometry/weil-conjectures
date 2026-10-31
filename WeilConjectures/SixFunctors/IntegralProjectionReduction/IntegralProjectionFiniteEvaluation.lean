/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionFiniteEvaluationData
public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionTensorEvaluation
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionSupportEvaluation
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionPullEvaluation
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionSystemEvaluation

/-! # Finite evaluation of the system projection expression

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
  CompactSupportFiniteProjection.tensor evaluatedSource evaluatedTarget evaluatedInput
  evaluatedSupport evaluatedPull liftedTensorEvaluation
  CompactSupportFiniteProjection.component compactSupportProjectionComponent
  compactSupportProperProjection
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  CompactSupportFiniteProjection.partialTensor torReduction

/-- Naturality of tensor evaluation, with independently specified endpoint squares. -/
private theorem tensor_evaluation_square
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (U : B × B ⥤ B) (F : A ⥤ B)
    (b : T ⋙ F ≅ F.prod F ⋙ U)
    {x x' y y' : A} {a a' c c' : B}
    (s : F.obj x ≅ a) (s' : F.obj x' ≅ a')
    (t : F.obj y ≅ c) (t' : F.obj y' ≅ c')
    (v : x ⟶ x') (w : y ⟶ y') (v' : a ⟶ a') (w' : c ⟶ c')
    (hv : F.map v ≫ s'.hom = s.hom ≫ v')
    (hw : F.map w ≫ t'.hom = t.hom ≫ w') :
    F.map (T.map (Prod.mkHom v w)) ≫ b.hom.app (x', y') ≫
        U.map (Prod.mkHom s'.hom t'.hom) =
      b.hom.app (x, y) ≫ U.map (Prod.mkHom s.hom t.hom) ≫
        U.map (Prod.mkHom v' w') := by
  have hb := b.hom.naturality (Prod.mkHom v w)
  dsimp only [Functor.comp_map, Functor.prod_map] at hb
  rw [← Category.assoc, hb]
  simp only [Category.assoc]
  rw [← U.map_comp, ← U.map_comp]
  apply congrArg (fun k ↦ b.hom.app (x, y) ≫ U.map k)
  exact Prod.hom_ext hv hw

/-- Naturality of support evaluation through the prescribed finite realization. -/
private theorem support_evaluation_square
    {A B A' B' C D : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category C] [Category D]
    (F : A ⥤ B) (G : A' ⥤ B') (H : C ⥤ D)
    (ev : A ⥤ A') (ev' : B ⥤ B') (I : C ⥤ A') (I' : D ⥤ B')
    (η : F ⋙ ev' ≅ ev ⋙ G) (θ : H ⋙ I' ≅ I ⋙ G)
    {M N : A} {P Q : C} (a : ev.obj M ≅ I.obj P) (b : ev.obj N ≅ I.obj Q)
    (v : M ⟶ N) (w : P ⟶ Q)
    (h : ev.map v ≫ b.hom = a.hom ≫ I.map w) :
    ev'.map (F.map v) ≫ (η.app N ≪≫ G.mapIso b ≪≫ θ.symm.app Q).hom =
      (η.app M ≪≫ G.mapIso a ≪≫ θ.symm.app P).hom ≫ I'.map (H.map w) := by
  have hη := η.hom.naturality v
  have hθ := θ.inv.naturality w
  dsimp only [Functor.comp_map] at hη hθ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hη]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, h, G.map_comp, Category.assoc]
  rw [← hθ]

set_option maxHeartbeats 1000000 in
-- Extra elaboration budget for tensor restrictions and full inclusions in both endpoint diagrams.
/-- Evaluate the system tensor and compactification projection, retaining the fixed
support and pullback coefficient coordinates. This statement contains no integral
projection map: its three equations concern the two endpoint maps and the system map.

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions;
coefficient evaluation and the prescribed coefficient adjunction comparisons.
(blueprint: lem-sf-integral-projection-finite-evaluation).

Proof: obtain the ambient system tensor comparison b and its proper/open projection
identity from integralProjectionSystemEvaluation. Compose b with datumTensorReduction
and reductionEvaluation on both inputs. The explicit partial tensor is a restriction
of the same ambient tensor, so the currying counit identifies its included functor.
Fullness and faithfulness of finiteInclusion lift this comparison to a natural e;
liftedTensorEvaluation_square computes its components. Choose evaluatedSource and
evaluatedTarget as the endpoint isomorphisms. For the source, tensor naturality and
the unary integralProjectionSupportEvaluation identity identify sourceMap with
sourceIso. For the tensor/pullback input, tensor naturality and the unary
integralProjectionPullEvaluation identity give tensorPullIso. Naturality of
supportEvaluation transports this identity through support; apply the support
identity to the integral tensor input to obtain targetIso. The proper/open system
identity supplied with b is exactly the third equation in these endpoint coordinates.
The construction retains every prescribed adjunction map and uses no inference from
equality of arbitrary finite evaluations. It applies equally to zero inputs,
identity/empty opens and the first quotient m = 0. -/
theorem integralProjectionFiniteEvaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o) :
    ∃ e : TensorComparison d m,
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        let t := tensorCoordinates d m e
        let ev := evaluation (C := C) (E := E) m Y
        let I := finiteInclusion (C := C) (E := E) m Y
        let KF := (reduction d m X).obj K
        let LF := (torReduction d m Y).obj L
        let T := CompactSupportFiniteProjection.partialTensor (stage d m)
        let A := ((d.higher.integralTensor Y).obj
          ((d.higher.integral.support f c).obj K)).obj L
        let B := (d.higher.integral.support f c).obj
          (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))
        ∃ (s : ev.obj (systemSource o f c K L) ≅
            I.obj (((T Y).obj (((stage d m).finite.support f c).obj KF)).obj LF))
          (r : ev.obj (systemTarget o f c K L) ≅
            I.obj (((stage d m).finite.support f c).obj
              (((T X).obj KF).obj
                ((CompactSupportFiniteProjection.torPull (stage d m) f).obj LF)))),
          ev.map (FixProjectionCompactification.Coordinates.sourceMap
              D C E d.higher hl o z f c K L) ≫ s.hom =
            (reductionEvaluation d m Y A).hom ≫ I.map (sourceIso d m t f c K L).hom ∧
          ev.map (FixProjectionCompactification.Coordinates.targetMap
              D C E d.higher hl o z f c K L) ≫ r.hom =
            (reductionEvaluation d m Y B).hom ≫ I.map (targetIso d m t f c K L).hom ∧
          ev.map (compactificationProjection C.l E o z.compositors z.openComparisons c
              ((calculus C.l E X.obj.left).reduction.obj K.obj)
              ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≫ r.hom =
            s.hom ≫ I.map (CompactSupportFiniteProjection.component (stage d m) f c
              KF LF) := by
  obtain ⟨b, hb⟩ := integralProjectionSystemEvaluation d m o z
  let e := liftedTensorEvaluation d m hl b
  refine ⟨e, ?_⟩
  intro X Y f _ _ _ c K L
  let t := tensorCoordinates d m e
  let ev := evaluation (C := C) (E := E) m Y
  let I := finiteInclusion (C := C) (E := E) m Y
  refine ⟨evaluatedSource d m b o f c K L, evaluatedTarget d m b o f c K L,
    ?_, ?_, hb f c K L⟩
  · have hs := integralProjectionSupportEvaluation d m hl o z f c K
    have hn := tensor_evaluation_square
      (calculus C.l E Y.obj.left).systemClosed.tensor
      (evaluatedTensor (C := C) (E := E) m Y) ev (b Y)
      (reductionEvaluation d m Y ((d.higher.integral.support f c).obj K))
      (evaluatedSupport d m o f c K)
      (reductionEvaluation d m Y L) (reductionEvaluation d m Y L)
      (FixProjectionCompactification.Coordinates.supportReduction
        D C E d.higher hl o z f c K) (𝟙 _)
      (I.map (((d.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K))
      (𝟙 _) hs (by simp)
    dsimp only [FixProjectionCompactification.Coordinates.sourceMap]
    simp only [Functor.map_comp, Category.assoc]
    change ev.map
      (FixProjectionCompactification.Coordinates.datumTensorReduction D C E
        d.higher hl Y ((d.higher.integral.support f c).obj K) L).hom ≫
      ev.map ((calculus C.l E Y.obj.left).systemClosed.tensor.map
        (Prod.mkHom (FixProjectionCompactification.Coordinates.supportReduction
          D C E d.higher hl o z f c K) (𝟙 _))) ≫
      (evaluatedSource d m b o f c K L).hom = _
    unfold evaluatedSource
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom,
      Functor.comp_obj, ObjectProperty.ι_obj]
    rw [hn]
    have hT := liftedTensorEvaluation_square d m hl b Y
      ((d.higher.integral.support f c).obj K) L
    have hTC := congrArg (fun q ↦ q ≫
      (evaluatedTensor (C := C) (E := E) m Y).map
        (Prod.mkHom
          (I.map (((d.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K))
          (𝟙 _))) hT
    simp only [Category.assoc] at hTC
    refine hTC.trans ?_
    dsimp only [I]
    simp only [sourceIso, Iso.trans_hom, Functor.map_comp]
    erw [partialTensor_map_left d m Y
      (((d.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K)
      ((torReduction d m Y).obj L)]
  · have hs := integralProjectionSupportEvaluation d m hl o z f c
      (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))
    have hp := integralProjectionPullEvaluation d m hl o z f L
    have hi :
        (evaluation (C := C) (E := E) m X).map
            (FixProjectionCompactification.Coordinates.inputReduction
              D C E d.higher hl o z f K L).inv ≫
          (evaluatedInput d m b f K L).hom =
        (reductionEvaluation d m X
          (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))).hom ≫
          (finiteInclusion (C := C) (E := E) m X).map
            (tensorPullIso d m t f K L).hom := by
      let evX := evaluation (C := C) (E := E) m X
      let p := (calculus C.l E X.obj.left).reduction.mapIso
          (FixProjectionCompactification.Coordinates.pullValue D C E d.higher hl f L) ≪≫
        FixProjectionCompactification.Coordinates.pullReduction D C E o z f.hom.left L.obj
      have hd :
          (FixProjectionCompactification.Coordinates.inputReduction
            D C E d.higher hl o z f K L).inv =
          (FixProjectionCompactification.Coordinates.datumTensorReduction D C E
            d.higher hl X K ((d.higher.integral.pull f).obj L)).hom ≫
            (calculus C.l E X.obj.left).systemClosed.tensor.map
              (Prod.mkHom (𝟙 _) p.hom) := by
        simp [FixProjectionCompactification.Coordinates.inputReduction, p]
      have hn := tensor_evaluation_square
        (calculus C.l E X.obj.left).systemClosed.tensor
        (evaluatedTensor (C := C) (E := E) m X) evX (b X)
        (reductionEvaluation d m X K) (reductionEvaluation d m X K)
        (reductionEvaluation d m X ((d.higher.integral.pull f).obj L))
        (evaluatedPull d m f L) (𝟙 _) p.hom (𝟙 _)
        ((finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map
          (pullIso d m f L).hom) (by simp) hp
      rw [hd, Functor.map_comp]
      unfold evaluatedInput
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom,
        Functor.comp_obj, ObjectProperty.ι_obj]
      simp only [Category.assoc]
      rw [hn]
      have hT := liftedTensorEvaluation_square d m hl b X K
        ((d.higher.integral.pull f).obj L)
      have hTC := congrArg (fun q ↦ q ≫
        (evaluatedTensor (C := C) (E := E) m X).map
          (Prod.mkHom (𝟙 _)
            ((finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map
              (pullIso d m f L).hom))) hT
      simp only [Category.assoc] at hTC
      refine hTC.trans ?_
      simp only [tensorPullIso, Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom]
      erw [partialTensor_map_right d m X ((reduction d m X).obj K) (pullIso d m f L).hom]
    have ht := support_evaluation_square
      (Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g)
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c)
      ((stage d m).finite.support f c)
      (evaluation (C := C) (E := E) m X) ev
      (finiteInclusion (C := C) (E := E) m X) I
      (supportEvaluation C.l E o c m) ((stage d m).finiteSupport f c)
      (reductionEvaluation d m X
        (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L)))
      (evaluatedInput d m b f K L)
      (FixProjectionCompactification.Coordinates.inputReduction
        D C E d.higher hl o z f K L).inv (tensorPullIso d m t f K L).hom hi
    have ht' :
        ev.map ((Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g).map
          (FixProjectionCompactification.Coordinates.inputReduction
            D C E d.higher hl o z f K L).inv) ≫
          (evaluatedTarget d m b o f c K L).hom =
        (evaluatedSupport d m o f c
          (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))).hom ≫
          I.map (((stage d m).finite.support f c).map (tensorPullIso d m t f K L).hom) := by
      unfold evaluatedTarget evaluatedSupport
      exact ht
    dsimp only [FixProjectionCompactification.Coordinates.targetMap]
    simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
    have hC := congrArg (fun q ↦ ev.map
      (FixProjectionCompactification.Coordinates.supportReduction D C E d.higher hl o z f c
        (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))) ≫ q) ht'
    have hsC := congrArg (fun q ↦ q ≫
      I.map (((stage d m).finite.support f c).map (tensorPullIso d m t f K L).hom)) hs
    simp only [Functor.comp_map] at hC
    simp only [Category.assoc] at hsC
    refine hC.trans (hsC.trans ?_)
    simp only [targetIso, Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom]
    rfl

end WeilConjectures.IntegralProjectionReduction
