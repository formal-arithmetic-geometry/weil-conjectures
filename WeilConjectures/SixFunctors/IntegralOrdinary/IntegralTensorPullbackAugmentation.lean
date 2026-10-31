/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorReductionAugmentation
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralReductionTensorPullback

/-! # The tensor/pullback square before inverting completion

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Stacks 07A4 and 0941. This square involves the forward augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem limit_tensor_augmentation
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    {LY : C ⥤ A} {RY : A ⥤ C} {LX : D ⥤ B} {RX : B ⥤ D}
    (adjY : LY ⊣ RY) (adjX : LX ⊣ RX) (P : A ⥤ B) (t : B × B ⥤ B)
    {S M N : C} {V T FM FN : D} {U : A} (bY : LY.obj S ⟶ U)
    (bX : LX.obj T ⟶ t.obj (LX.obj FM, LX.obj FN))
    (aS : LX.obj V ⟶ P.obj (LY.obj S))
    (aM : LX.obj FM ⟶ P.obj (LY.obj M)) (aN : LX.obj FN ⟶ P.obj (LY.obj N))
    (v : V ⟶ T) (w : P.obj U ⟶ t.obj (P.obj (LY.obj M), P.obj (LY.obj N)))
    [IsIso (adjX.counit.app (P.obj (LY.obj M)))]
    [IsIso (adjX.counit.app (P.obj (LY.obj N)))]
    (hc : aS ≫ P.map bY ≫ w =
      LX.map v ≫ bX ≫ t.map (Prod.mkHom aM aN)) :
    adjX.unit.app V ≫ RX.map aS ≫
        RX.map (P.map (LY.map (adjY.unit.app S ≫ RY.map bY))) ≫
        RX.map (P.map (adjY.counit.app U)) ≫ RX.map w ≫
        RX.map (t.map (Prod.mkHom
          (inv (adjX.counit.app (P.obj (LY.obj M))))
          (inv (adjX.counit.app (P.obj (LY.obj N)))))) =
      v ≫ adjX.unit.app T ≫ RX.map bX ≫
        RX.map (t.map (Prod.mkHom
          (LX.map (adjX.unit.app FM ≫ RX.map aM))
          (LX.map (adjX.unit.app FN ≫ RX.map aN)))) := by
  have hy : LY.map (adjY.unit.app S ≫ RY.map bY) ≫ adjY.counit.app U = bY := by
    simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] using
      (adjY.homEquiv S U).symm_apply_apply bY
  have hm : LX.map (adjX.unit.app FM ≫ RX.map aM) =
      aM ≫ inv (adjX.counit.app (P.obj (LY.obj M))) := by
    apply (cancel_mono (adjX.counit.app (P.obj (LY.obj M)))).1
    simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
      (adjX.homEquiv FM (P.obj (LY.obj M))).symm_apply_apply aM
  have hn : LX.map (adjX.unit.app FN ≫ RX.map aN) =
      aN ≫ inv (adjX.counit.app (P.obj (LY.obj N))) := by
    apply (cancel_mono (adjX.counit.app (P.obj (LY.obj N)))).1
    simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
      (adjX.homEquiv FN (P.obj (LY.obj N))).symm_apply_apply aN
  have hs : aS ≫ P.map (LY.map (adjY.unit.app S ≫ RY.map bY)) ≫
      P.map (adjY.counit.app U) ≫ w ≫
        t.map (Prod.mkHom (inv (adjX.counit.app (P.obj (LY.obj M))))
          (inv (adjX.counit.app (P.obj (LY.obj N))))) =
      LX.map v ≫ bX ≫ t.map (Prod.mkHom
        (LX.map (adjX.unit.app FM ≫ RX.map aM))
        (LX.map (adjX.unit.app FN ≫ RX.map aN))) := by
    have hpy : P.map (LY.map (adjY.unit.app S ≫ RY.map bY)) ≫
        P.map (adjY.counit.app U) = P.map bY := by
      rw [← P.map_comp, hy]
    calc
      _ = (aS ≫ P.map bY ≫ w) ≫
          t.map (Prod.mkHom (inv (adjX.counit.app (P.obj (LY.obj M))))
            (inv (adjX.counit.app (P.obj (LY.obj N))))) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ aS ≫ z ≫ w ≫ t.map (Prod.mkHom
            (inv (adjX.counit.app (P.obj (LY.obj M))))
            (inv (adjX.counit.app (P.obj (LY.obj N)))))) hpy
      _ = _ := by
        rw [hc, hm, hn]
        simp only [Category.assoc, ← t.map_comp]
        rfl
  have hr := congrArg (fun z ↦ adjX.unit.app V ≫ RX.map z) hs
  simp only [Functor.map_comp, Category.assoc] at hr ⊢
  have hu := adjX.unit.naturality v
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc (adjX.unit.app V) (RX.map (LX.map v)), ← hu] at hr
  simpa only [Category.assoc] using hr

/-- The canonical completed comparison commutes with the forward quotient augmentations.
This is a component equation for specified maps, without constructing any isomorphism
on constructible subcategories and without higher-operation data or properness.

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Stacks 07A4 and 0941.
(blueprint: lem-sf-integral-tensor-pullback-augmentation).

Proof: resolve both constructible inputs simultaneously by flat-term K-flat complexes.
Replace each tensor augmentation by its defining representative equation and replace
pullComparison by pullIso followed by the normalized ordinary pullback augmentation.
The module adjunction uniqueness defining pullIso preserves the adjunction-unit
sections. At quotient exponent n+1, the two composites send a homogeneous pure tensor
x tensor y to the tensor of the pullbacks of 1 tensor x and 1 tensor y. Balancing,
naturality of the scalar unit and the ordinary tensor-pullback normalization make
these maps equal; the quotient transition equations give equality of entire strict
towers. The maps from total tensor to each strict Roos cone have those same product
components and zero shifted component. Product and mapping-cocone extensionality
therefore prove equality of chain maps. The definition of the canonical completed
comparison is the derived-limit image of this coherent tensor comparison, conjugated
by the specified reduction/limit counits. Substitute those counits and cancel their
inverse pairs by the adjunction triangle identities. Faithful whiskering by the
product of the good-complex localizations descends the representative equality to
the displayed derived equality. This applies also to zero inputs and empty schemes;
no inference of equality from individual derived evaluations is used. -/
theorem tensorPullback_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (τX : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X)
    (τY : (tensorModel l E Y).tensor ⟶ integralCompletedTensor l E Y)
    (hX : TensorAugmentationNormalized l E X τX)
    (hY : TensorAugmentationNormalized l E Y τY)
    (M N : sfIntegralConstructibleCategory l E Y) :
    (PurCompactSupport.pull (PurCompactSupport.completed l E) f).map
        (τY.app (M.obj, N.obj)) ≫
      (pullComparison l E f).app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
      ((canonicalIntegralPullbackTensor l E f M N).hom).hom =
    (proEtaleCanonicalTensorComparison f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)
        (tensorModel l E Y) (tensorModel l E X)).hom.app (M.obj, N.obj) ≫
      τX.app
        ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj M.obj,
          (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj N.obj) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((pullComparison l E f).app M.obj)
          ((pullComparison l E f).app N.obj)) := by
  let CY := pullbackTensorCalculus l E Y
  let CX := pullbackTensorCalculus l E X
  let O := PurCompactSupport.pull (PurCompactSupport.completed l E) f
  let G := integralDerivedPullback l E f
  let H := pullbackTensorReferencePullback l E f
  let U := pullbackTensorReferenceTensor l E X
  let a := pullbackReductionComparison l E f
  let bX := tensorReductionComparison l E X
  let bY := tensorReductionComparison l E Y
  let e := pullbackTensorIntegralPullbackModel l E f
  let dX := pullbackTensorIntegralTensorModel l E X
  let dY := pullbackTensorIntegralTensorModel l E Y
  let ρ := pullComparison l E f
  let v := (proEtaleCanonicalTensorComparison f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)
    (tensorModel l E Y) (tensorModel l E X)).hom.app (M.obj, N.obj)
  have ha := (pullbackReductionAugmentation_existsUnique l E f).exists.choose_spec
  have hbX := (tensorReductionAugmentation_existsUnique l E X).exists.choose_spec τX hX
  have hbY := (tensorReductionAugmentation_existsUnique l E Y).exists.choose_spec τY hY
  have hε := pullbackTensorComparisonCounits l E f M N
  have := hε.1
  have := hε.2.1
  have := hε.2.2
  have hformal := limit_tensor_augmentation CY.adjunction CX.adjunction
    (pullbackTensorSequenceDerived l E f) CX.systemClosed.tensor
    (bY.hom.app (M.obj, N.obj)) (bX.hom.app (O.obj M.obj, O.obj N.obj))
    (a.hom.app ((tensorModel l E Y).tensor.obj (M.obj, N.obj)))
    (a.hom.app M.obj) (a.hom.app N.obj) v
    ((pullbackTensorSystemComparison l E f).hom.app
      (CY.reduction.obj M.obj, CY.reduction.obj N.obj))
    (reductionTensorPullback l E f M.obj N.obj)
  have href : (ρ.app ((tensorModel l E Y).tensor.obj (M.obj, N.obj)) ≫
        e.hom.app ((tensorModel l E Y).tensor.obj (M.obj, N.obj))) ≫
      H.map (τY.app (M.obj, N.obj) ≫ dY.hom.app (M.obj, N.obj)) ≫
      (pullbackTensorReferenceComparison l E f M N).hom =
    v ≫ (τX.app (O.obj M.obj, O.obj N.obj) ≫
      dX.hom.app (O.obj M.obj, O.obj N.obj)) ≫
      U.map (Prod.mkHom (ρ.app M.obj ≫ e.hom.app M.obj)
        (ρ.app N.obj ≫ e.hom.app N.obj)) := by
    dsimp only [ρ, e, dX, dY, O, H, U]
    rw [ha, hbY, hbX, ha, ha]
    dsimp only [CX, CY, O, a, bX, bY, pullbackReductionComparison,
      tensorReductionComparison] at hformal
    simpa only [pullbackTensorReferenceComparison, pullbackTensorReferencePullback,
      pullbackTensorReferenceTensor, Functor.comp_map, Functor.prod_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom,
      asIso_hom, asIso_inv, Iso.prod_hom, Iso.prod_inv, Iso.app_hom,
      Category.assoc] using hformal
  let z := U.mapIso (Iso.prod (e.app M.obj) (e.app N.obj))
  let q := dX.hom.app (G.obj M.obj, G.obj N.obj) ≫ z.hom
  have hcanonical : ((canonicalIntegralPullbackTensor l E f M N).hom).hom ≫ q =
      e.hom.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        H.map (dY.hom.app (M.obj, N.obj)) ≫
          (pullbackTensorReferenceComparison l E f M N).hom := by
    change (e.hom.app _ ≫ H.map (dY.hom.app _) ≫
      (pullbackTensorReferenceComparison l E f M N).hom ≫ z.inv ≫
      dX.inv.app (G.obj M.obj, G.obj N.obj)) ≫
      (dX.hom.app (G.obj M.obj, G.obj N.obj) ≫ z.hom) = _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hnat := dX.hom.naturality (Prod.mkHom (ρ.app M.obj) (ρ.app N.obj))
  have hrnat := ρ.naturality (τY.app (M.obj, N.obj))
  have hz : U.map (Prod.mkHom (ρ.app M.obj) (ρ.app N.obj)) ≫ z.hom =
      U.map (Prod.mkHom (ρ.app M.obj ≫ e.hom.app M.obj)
        (ρ.app N.obj ≫ e.hom.app N.obj)) := by
    change U.map _ ≫ U.map (Prod.mkHom (e.hom.app M.obj) (e.hom.app N.obj)) = _
    rw [← U.map_comp]
    rfl
  apply (cancel_mono q).1
  change (O.map (τY.app (M.obj, N.obj)) ≫ ρ.app _ ≫
      ((canonicalIntegralPullbackTensor l E f M N).hom).hom) ≫ q =
    (v ≫ τX.app (O.obj M.obj, O.obj N.obj) ≫
      (integralCompletedTensor l E X).map (Prod.mkHom (ρ.app M.obj) (ρ.app N.obj))) ≫ q
  rw [Category.assoc, Category.assoc, hcanonical]
  dsimp only [q]
  simp only [Category.assoc]
  rw [← Category.assoc ((integralCompletedTensor l E X).map _) (dX.hom.app _), hnat]
  simp only [Category.assoc]
  rw [hz]
  have he := e.hom.naturality (τY.app (M.obj, N.obj))
  have he' : (ρ.app ((tensorModel l E Y).tensor.obj (M.obj, N.obj)) ≫
      e.hom.app ((tensorModel l E Y).tensor.obj (M.obj, N.obj))) ≫
      H.map (τY.app (M.obj, N.obj)) =
    (O.map (τY.app (M.obj, N.obj)) ≫ ρ.app _) ≫ e.hom.app _ := by
    rw [Category.assoc, ← he, ← Category.assoc, ← hrnat]
  rw [H.map_comp] at href
  simp only [← Category.assoc] at href ⊢
  rw [he'] at href
  exact href

end WeilConjectures.IntegralOrdinary
