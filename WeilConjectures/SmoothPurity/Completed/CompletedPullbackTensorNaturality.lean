/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison

/-! # Naturality of the localized canonical pullback/tensor comparison

The canonical rational comparison `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` is natural in `M` and `N`.

## Implementation details

The integral comparison is a natural isomorphism; after scalar localization, on pure tensors
`a ⊗ f` and `b ⊗ g` both sides equal `ab ⊗` the same integral composite, and bilinearity
extends this to all rational arrows.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  pullbackTensorCalculus integralDerivedPullback integralCompletedTensor

private def integralComparisonIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralTensor l E Y ⋙ constructibleIntegralPullback l E f ≅
      (constructibleIntegralPullback l E f).prod (constructibleIntegralPullback l E f) ⋙
        constructibleIntegralTensor l E X := by
  let I := (sfIntegralConstructible l E Y).ι
  let R := I ⋙ (pullbackTensorCalculus l E Y).reduction
  let F := pullbackTensorSequenceDerived l E f
  let LY := coefficientSequenceLimit l E Y
  let LX := coefficientSequenceLimit l E X
  let TY := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let RX := (pullbackTensorCalculus l E X).reduction
  let P := I ⋙ integralDerivedPullback l E f
  let a : P ≅ R ⋙ F ⋙ LX :=
    Functor.isoWhiskerLeft I (pullbackTensorIntegralPullbackModel l E f)
  let b : (I.prod I) ⋙ integralCompletedTensor l E Y ≅ (R.prod R) ⋙ TY ⋙ LY :=
    Functor.isoWhiskerLeft (I.prod I) (pullbackTensorIntegralTensorModel l E Y)
  let cy : (R.prod R) ⋙ TY ⋙ LY ⋙ (pullbackTensorCalculus l E Y).reduction ≅
      (R.prod R) ⋙ TY :=
    NatIso.ofComponents (fun MN ↦ by
      letI : IsIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
          (TY.obj (R.obj MN.1, R.obj MN.2))) :=
        (pullbackTensorComparisonCounits l E f MN.1 MN.2).1
      exact asIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
        (TY.obj (R.obj MN.1, R.obj MN.2))))
      (by
        intro MN MN' g
        simpa only [LY, Functor.comp_map, Functor.prod_map, Functor.id_map, asIso_hom] using
          (pullbackTensorCalculus l E Y).adjunction.counit.naturality
            (TY.map (Prod.mkHom (R.map g.1) (R.map g.2))))
  let cx : R ⋙ F ⋙ LX ⋙ RX ≅ R ⋙ F :=
    NatIso.ofComponents (fun M ↦ by
      letI : IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
          (F.obj (R.obj M))) := (pullbackTensorComparisonCounits l E f M M).2.1
      exact asIso ((pullbackTensorCalculus l E X).adjunction.counit.app (F.obj (R.obj M))))
      (by
        intro M M' g
        simpa only [LX, RX, Functor.comp_map, Functor.id_map, asIso_hom] using
          (pullbackTensorCalculus l E X).adjunction.counit.naturality (F.map (R.map g)))
  let e : ((I.prod I) ⋙ integralCompletedTensor l E Y) ⋙ integralDerivedPullback l E f ≅
      (P.prod P) ⋙ integralCompletedTensor l E X :=
    Functor.isoWhiskerLeft ((I.prod I) ⋙ integralCompletedTensor l E Y)
        (pullbackTensorIntegralPullbackModel l E f) ≪≫
      Functor.isoWhiskerRight b
        ((pullbackTensorCalculus l E Y).reduction ⋙ F ⋙ LX) ≪≫
      Functor.isoWhiskerRight cy (F ⋙ LX) ≪≫
      Functor.isoWhiskerLeft (R.prod R)
        (Functor.isoWhiskerRight (pullbackTensorSystemComparison l E f) LX) ≪≫
      Functor.isoWhiskerRight (NatIso.prod cx.symm cx.symm) (TX ⋙ LX) ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerRight a.symm RX)
          (Functor.isoWhiskerRight a.symm RX)) (TX ⋙ LX) ≪≫
      Functor.isoWhiskerLeft (P.prod P) (pullbackTensorIntegralTensorModel l E X).symm
  exact NatIso.ofComponents
    (fun MN ↦ ObjectProperty.isoMk _ (e.app MN))
    (fun g ↦ ObjectProperty.hom_ext _ (e.hom.naturality g))

attribute [local implicit_reducible] pullbackTensorReferenceTensor
  pullbackTensorReferencePullback constructibleIntegralTensor constructibleIntegralPullback
  scalarReductionSourceDerived in
private theorem integralComparisonIso_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonIso l E f).app (M,N) =
      canonicalIntegralPullbackTensor l E f M N := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  simp only [integralComparisonIso, canonicalIntegralPullbackTensor,
    pullbackTensorReferenceComparison, ObjectProperty.isoMk, Iso.app_hom, Iso.app_inv,
    ObjectProperty.ι_obj,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, NatIso.prod_hom, NatTrans.prod,
    asIso_hom, asIso_inv, Iso.prod_hom, ObjectProperty.homMk,
    pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
    Functor.comp_obj, Functor.prod_obj, Functor.comp_map, Functor.prod_map,
    Category.assoc]

/-- The canonical rational comparison `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` is natural in both
inputs. -/
theorem canonicalRationalPullbackTensor_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {M M' N N' : sfRationalConstructibleCategory l E Y} (a : M ⟶ M') (b : N ⟶ N') :
    (rationalDerivedPullback l E f).map
        ((rationalDerivedTensor l E Y).map (Prod.mkHom a b)) ≫
      (canonicalRationalPullbackTensor l E f M' N').hom =
    (canonicalRationalPullbackTensor l E f M N).hom ≫
      (rationalDerivedTensor l E X).map
        (Prod.mkHom ((rationalDerivedPullback l E f).map a)
          ((rationalDerivedPullback l E f).map b)) := by
  let U := constructibleIntegralTensor l E Y
  let V := constructibleIntegralTensor l E X
  let r := constructibleIntegralPullback l E f
  let A := rationalDerivedTensor l E Y
  let B := rationalDerivedTensor l E X
  let T := rationalDerivedPullback l E f
  have hT := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have hA := (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec
  have hB := (rationalDerivedTensor_existsUnique l E X).exists.choose_spec
  let _ : T.Additive := hT.1
  obtain ⟨e, he, _⟩ := OperationsScalarLocalization.bilinearComparison_existsUnique
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l E)
    (RingHom.id _) U V r A B T hA.1 hB.1 hT.2.1 hT.2.2 hA.2 hB.2
    (integralComparisonIso l E f)
  have happ (M N : sfRationalConstructibleCategory l E Y) :
      e.app (M,N) = canonicalRationalPullbackTensor l E f M N := by
    apply Iso.ext
    apply eq_of_heq
    have h := he (M,N)
    rw [show (integralComparisonIso l E f).hom.app (M.obj,N.obj) =
      (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom from
        congrArg Iso.hom (integralComparisonIso_app l E f M.obj N.obj)] at h
    exact h.trans
      ((canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec).symm
  have h := e.hom.naturality (Prod.mkHom a b)
  change T.map (A.map (Prod.mkHom a b)) ≫ (e.app (M',N')).hom =
    (e.app (M,N)).hom ≫ B.map (Prod.mkHom (T.map a) (T.map b)) at h
  rw [happ, happ] at h
  exact h

end WeilConjectures
