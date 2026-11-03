/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorPresentationComparison
public import WeilConjectures.PoincareDuality.ReindexingSystemHomReductionSquare
import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorPresentationAugmentation
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorSquareOfHomSquare
import all WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorPullbackAugmentation

/-! # The integral quotient-completion reindexing square

Source: BS Remark 6.8.15; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local implicit_reducible] constructibleIntegralTensor constructibleIntegralPullback
variable (l : ℕ) [Fact l.Prime]

/-- The normalized quotient-completion maps commute with integral inverse image.
This equation concerns integral coefficient operations only, with no realization
or scalar-extension tensor comparison.
Source: BS Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 0941.
(blueprint: lem-sf-adic-tensor-completion-reindexing).

Proof: identify each normalized presentation with the reduction adjunct. On good
representatives, uniqueness of the strict augmentation identifies its cochain map
with the ringed model's map; fully faithful restriction descends this equality.
The ambient internal-Hom reduction square implies the reduction tensor square:
transpose the identity tensor map, use compatibility of closed base change with
transposition, and uncurry. Apply reduction/limit adjunction compatibility to this
square. Naturality of the unit and the counit's triangle identity give precisely
the reference tensor comparison defining canonicalIntegralPullbackTensor. Cancel
the fixed tensor-model and pullback-model isomorphisms. Naturality of the completed
tensor augmentation moves the two complete-input identifications to the required
side. The argument imposes no restriction on torsion or zero inputs. -/
theorem tensor_completion_reindexing
    (k : Type u) [Field k] [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (NX : ConstructibleTensorCompletionPresentation l k X)
    (NY : ConstructibleTensorCompletionPresentation l k Y)
    (K L : sfIntegralConstructibleCategory l k Y) :
    let H := podCompletedDerivedInverseImage l k g
    let TX := (pullbackTensorCalculus l k X).integralClosed.tensor
    let TY := constructibleIntegralTensor l k Y
    let P := constructibleIntegralPullback l k g
    H.map ((tensorPresentationCompletion l k Y NY).app (K.obj, L.obj)) ≫
        (podCompletedToTowerIso l k g (TY.obj (K, L))).hom ≫
        (canonicalIntegralPullbackTensor l k g K L).hom.hom =
      (podCompletedAmbientTensor l k g).hom.app (K.obj, L.obj) ≫
        TX.map (Prod.mkHom (podCompletedToTowerIso l k g K).hom
          (podCompletedToTowerIso l k g L).hom) ≫
        (tensorPresentationCompletion l k X NX).app ((P.obj K).obj, (P.obj L).obj) := by
  dsimp only
  let CY := pullbackTensorCalculus l k Y
  let CX := pullbackTensorCalculus l k X
  let F := podCompletedDerivedInverseImage l k g
  let G := integralDerivedPullback l k g
  let B := pullbackTensorSequenceDerived l k g
  let H := pullbackTensorReferencePullback l k g
  let U := pullbackTensorReferenceTensor l k X
  let e := pullbackTensorIntegralPullbackModel l k g
  let dX := pullbackTensorIntegralTensorModel l k X
  let dY := pullbackTensorIntegralTensorModel l k Y
  let τX := tensorPresentationCompletion l k X NX
  let τY := tensorPresentationCompletion l k Y NY
  let μ := podCompletedAmbientTensor l k g
  let ρ : F ⟶ G :=
    { app := podCompletedToTower l k g
      naturality := fun _ _ f ↦ (podCompletedToTower_laws l k g).1 _ _ f }
  let a : F ⋙ CX.reduction ≅ CY.reduction ⋙ B :=
    NatIso.ofComponents (podReductionReindexing l k g)
      (fun f ↦ (podReductionReindexingMap_laws l k g).2 _ _ f)
  have hsys := podReindexingSystemHomReductionSquare_laws l k g
  have hred := coefficientTensorSquareOfCompositeHomSquare
    CY.integralClosed CX.integralClosed CY.systemClosed CX.systemClosed
    F B CY.reduction CX.reduction μ (pullbackTensorSystemComparison l k g)
    CY.reductionTensor CX.reductionTensor a (fun M N ↦ hsys.beta M N) K.obj L.obj
  have ha (M : DerivedCategory (integralTowerModules l k Y)) :
      ρ.app M ≫ e.hom.app M =
        CX.adjunction.unit.app (F.obj M) ≫
          (coefficientSequenceLimit l k X).map (a.hom.app M) := by
    change (F.map (CY.adjunction.unit.app M) ≫
      (podLimitReindexing l k g).inv.app (CY.reduction.obj M) ≫ e.inv.app M) ≫
        e.hom.app M = _
    calc
      _ = (F.map (CY.adjunction.unit.app M) ≫
          (podLimitReindexing l k g).inv.app (CY.reduction.obj M)) ≫
            (e.inv.app M ≫ e.hom.app M) := by simp only [Category.assoc]
      _ = F.map (CY.adjunction.unit.app M) ≫
          (podLimitReindexing l k g).inv.app (CY.reduction.obj M) := by
        rw [Iso.inv_hom_id_app]
        exact Category.comp_id _
      _ = _ := hsys.adjunction.unit M
  have hbX (M N : DerivedCategory (integralTowerModules l k X)) :
      τX.app (M, N) ≫ dX.hom.app (M, N) =
        CX.adjunction.unit.app (CX.integralClosed.tensor.obj (M, N)) ≫
          (coefficientSequenceLimit l k X).map (CX.reductionTensor.hom.app (M, N)) :=
    tensorPresentationCompletion_augmentation l k X NX M N
  have hbY (M N : DerivedCategory (integralTowerModules l k Y)) :
      τY.app (M, N) ≫ dY.hom.app (M, N) =
        CY.adjunction.unit.app (CY.integralClosed.tensor.obj (M, N)) ≫
          (coefficientSequenceLimit l k Y).map (CY.reductionTensor.hom.app (M, N)) :=
    tensorPresentationCompletion_augmentation l k Y NY M N
  have hε := pullbackTensorComparisonCounits l k g K L
  have := hε.1
  have := hε.2.1
  have := hε.2.2
  let v := μ.hom.app (K.obj, L.obj)
  have hformal := IntegralOrdinary.limit_tensor_augmentation CY.adjunction CX.adjunction
    B CX.systemClosed.tensor
    (CY.reductionTensor.hom.app (K.obj, L.obj))
    (CX.reductionTensor.hom.app (F.obj K.obj, F.obj L.obj))
    (a.hom.app (CY.integralClosed.tensor.obj (K.obj, L.obj)))
    (a.hom.app K.obj) (a.hom.app L.obj) v
    ((pullbackTensorSystemComparison l k g).hom.app
      (CY.reduction.obj K.obj, CY.reduction.obj L.obj)) hred
  have href : (ρ.app (CY.integralClosed.tensor.obj (K.obj, L.obj)) ≫
        e.hom.app (CY.integralClosed.tensor.obj (K.obj, L.obj))) ≫
      H.map (τY.app (K.obj, L.obj) ≫ dY.hom.app (K.obj, L.obj)) ≫
      (pullbackTensorReferenceComparison l k g K L).hom =
    v ≫ (τX.app (F.obj K.obj, F.obj L.obj) ≫
      dX.hom.app (F.obj K.obj, F.obj L.obj)) ≫
      U.map (Prod.mkHom (ρ.app K.obj ≫ e.hom.app K.obj)
        (ρ.app L.obj ≫ e.hom.app L.obj)) := by
    rw [ha, hbY, hbX, ha, ha]
    dsimp only [H, U]
    dsimp only [CX, CY, B] at hformal
    simpa only [pullbackTensorReferenceComparison, pullbackTensorReferencePullback,
      pullbackTensorReferenceTensor, Functor.comp_map, Functor.prod_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom,
      asIso_hom, asIso_inv, Iso.prod_hom, Iso.prod_inv, Iso.app_hom,
      Category.assoc] using hformal
  let z := U.mapIso (Iso.prod (e.app K.obj) (e.app L.obj))
  let q := dX.hom.app (G.obj K.obj, G.obj L.obj) ≫ z.hom
  have hcanonical : ((canonicalIntegralPullbackTensor l k g K L).hom).hom ≫ q =
      e.hom.app ((integralCompletedTensor l k Y).obj (K.obj, L.obj)) ≫
        H.map (dY.hom.app (K.obj, L.obj)) ≫
          (pullbackTensorReferenceComparison l k g K L).hom := by
    change (e.hom.app _ ≫ H.map (dY.hom.app _) ≫
      (pullbackTensorReferenceComparison l k g K L).hom ≫ z.inv ≫
      dX.inv.app (G.obj K.obj, G.obj L.obj)) ≫
      (dX.hom.app (G.obj K.obj, G.obj L.obj) ≫ z.hom) = _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hnat := dX.hom.naturality (Prod.mkHom (ρ.app K.obj) (ρ.app L.obj))
  have hrnat := ρ.naturality (τY.app (K.obj, L.obj))
  have hz : U.map (Prod.mkHom (ρ.app K.obj) (ρ.app L.obj)) ≫ z.hom =
      U.map (Prod.mkHom (ρ.app K.obj ≫ e.hom.app K.obj)
        (ρ.app L.obj ≫ e.hom.app L.obj)) := by
    change U.map _ ≫ U.map (Prod.mkHom (e.hom.app K.obj) (e.hom.app L.obj)) = _
    rw [← U.map_comp]
    rfl
  have haug : F.map (τY.app (K.obj, L.obj)) ≫ ρ.app _ ≫
      ((canonicalIntegralPullbackTensor l k g K L).hom).hom =
    v ≫ τX.app (F.obj K.obj, F.obj L.obj) ≫
      (integralCompletedTensor l k X).map (Prod.mkHom (ρ.app K.obj) (ρ.app L.obj)) := by
    apply (cancel_mono q).1
    rw [Category.assoc, Category.assoc, hcanonical]
    dsimp only [q]
    simp only [Category.assoc]
    rw [← Category.assoc ((integralCompletedTensor l k X).map _) (dX.hom.app _), hnat]
    simp only [Category.assoc]
    rw [hz]
    have he := e.hom.naturality (τY.app (K.obj, L.obj))
    have he' : (ρ.app (CY.integralClosed.tensor.obj (K.obj, L.obj)) ≫
        e.hom.app (CY.integralClosed.tensor.obj (K.obj, L.obj))) ≫
        H.map (τY.app (K.obj, L.obj)) =
      (F.map (τY.app (K.obj, L.obj)) ≫ ρ.app _) ≫ e.hom.app _ := by
      rw [Category.assoc, ← he, ← Category.assoc, ← hrnat]
    rw [H.map_comp] at href
    simp only [← Category.assoc] at href ⊢
    rw [he'] at href
    exact href
  have hn := τX.naturality (Prod.mkHom (ρ.app K.obj) (ρ.app L.obj))
  rw [← hn] at haug
  exact haug

end WeilConjectures.AdicQbarRealization
