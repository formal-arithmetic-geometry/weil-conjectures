/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicLisseFixed

/-! # Scalar realizations of finite perfect adic origins

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This is the realization part of
`finitePerfectAdic_descend_coordinate_transitions`.
(blueprint: new-w5-finite-perfect-adic-coordinate-realizations)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem compatible_normalized
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hc : FinitePerfectModelsCompatible X d φ) :
    FinitePerfectModelsNormalized X d φ := by
  intro n U a
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a.down
  cases a
  subst hb
  have h := congrArg (fun k ↦ (k.hom.app U).hom
    ((koszulConstantUnit X A).app U (ULift.up b))) (hc.2 n)
  let qlift : ULift.{t + 1} A →+* ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hq := congrArg (fun k ↦ (k.app U).hom (ULift.up b))
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom
        qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) b)) =
    (adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
      ((koszulConstantUnit X A).app U (ULift.up b)) at hq
  change (completedAdicProjection X d n).hom.app U
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicScalar X d)).hom.app U
        ((koszulConstantUnit X A).app U (ULift.up b))) =
    (φ n).hom.app U
      ((adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
        ((koszulConstantUnit X A).app U (ULift.up b))) at h
  rw [← hq] at h
  exact h.symm.trans ((completedAdicScalar_exists X d).exists.choose_spec n U (ULift.up b))

private def chartSiteIso
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) :
    (ProEt.sliceEquiv X W).functor ⋙
      MorphismProperty.Over.map ⊤ (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
      MorphismProperty.Over.map ⊤ U.prop ⋙
      MorphismProperty.Over.map ⊤ (show WeaklyEtale V.hom from inferInstance) ≅
        Over.forget W := by
  refine NatIso.ofComponents (fun Z ↦ MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_
  · change 𝟙 _ ≫ Z.left.hom = ((Z.hom.left ≫ f.left) ≫ U.hom) ≫ V.hom
    simp only [Category.id_comp, Category.assoc]
    change Z.left.hom = Z.hom.left ≫ (f.left ≫
      (finitePerfectAdicChartObject V U).hom)
    rw [MorphismProperty.Over.w f, MorphismProperty.Over.w Z.hom]
  · intro Z Z' g
    apply MorphismProperty.Over.Hom.ext
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl

private def chartFixedRestrictionIso
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) :
    have := ProEt.sliceDense X W
    let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
    let H := SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ) ⋙
      proEtaleModuleRestriction X B
    finiteCoefficientSliceRestriction X B R ψ V ⋙
      ProEtale.localizationRestriction D U.hom U.prop ⋙
      ProEtale.localizationRestriction D f.left
        (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
      ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
        (ProEt.topology W.left) D).inverse ≅
      H ⋙ (ProEt.topology X).overPullback D W := by
  have := ProEt.sliceDense X W
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let H := SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ) ⋙
    proEtaleModuleRestriction X B
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (NatIso.op (chartSiteIso X V U W f)).symm
      (H.obj M).obj)) ?_
  intro M N g
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Z
  exact ((H.map g).hom.naturality _).symm

private def normalizedSliceIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hn : FinitePerfectModelsNormalized X d φ) (W : X.ProEt) (n : ℕ) :
    (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (φ n)) ⋙
      proEtaleModuleRestriction X (A ⧸ d.ideal ^ (n + 1))) ⋙
      (ProEt.topology X).overPullback
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) W ≅
    SheafOfModules.overFunctor.{t + 1} (completedAdicFiniteRing X d n) W ⋙
      ConstantScalarComparison.restriction ((ProEt.topology X).over W)
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))
        ((completedAdicFiniteRing X d n).over W) (finitePerfectAdicSliceScalar X d W n) := by
  have hα : proEtaleModuleScalarUnit X (A ⧸ d.ideal ^ (n + 1)) ≫
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (φ n)).hom =
      ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n) := by
    ext Z a
    exact hn n Z a
  dsimp only [finitePerfectAdicSliceScalar]
  rw [← hα]
  exact NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun Z ↦ Iso.refl _)))

private def sliceCounitIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (W : X.ProEt) (n : ℕ) :
    ConstantScalarComparison.restriction ((ProEt.topology X).over W)
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))
        ((completedAdicFiniteRing X d n).over W) (finitePerfectAdicSliceScalar X d W n) ⋙
      finitePerfectAdicSliceModules X d W n ≅ 𝟭 _ := by
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  let adj := PresheafOfModules.sheafificationAdjunction.{t + 1}
    (finitePerfectAdicSliceScalar X d W n)
  refine NatIso.ofComponents (fun M ↦ asIso (adj.counit.app M)) ?_
  intro M N g
  exact adj.counit.naturality g

private def ordinaryRealizationIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hn : FinitePerfectModelsNormalized X d φ)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
        (completedAdicFiniteCommRing X d n) (φ n) V ⋙
      ProEtale.localizationRestriction
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom U.prop ⋙
      finitePerfectAdicScalarModules X d V U W f n ≅
    SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection X d n) ⋙
      SheafOfModules.overFunctor.{t + 1} (completedAdicRing X d) W := by
  have := ProEt.sliceDense X W
  let O := SheafOfModules.overFunctor.{t + 1} (completedAdicFiniteRing X d n) W
  let P := SheafOfModules.restrictScalars.{t + 1}
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicProjection X d n))
  let c := chartFixedRestrictionIso X (A ⧸ d.ideal ^ (n + 1))
    (completedAdicFiniteCommRing X d n) (φ n) V U W f ≪≫
      normalizedSliceIso X d φ hn W n
  exact Functor.isoWhiskerRight c (finitePerfectAdicSliceModules X d W n ⋙ P) ≪≫
    Functor.isoWhiskerLeft O (Functor.isoWhiskerRight (sliceCounitIso X d W n) P)

set_option linter.unusedVariables false in
/--
Each supplied finite quotient comparison admits the actual scalar-realization
isomorphisms on every chart and pro-etale restriction.

Source: Stacks Project, Tags 09C6 and 06YY.
(blueprint: new-w5-finite-perfect-adic-coordinate-realizations)
-/
theorem finitePerfectAdic_coordinate_realizations
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅
      finitePerfectAdicQuotientCoordinates X d φ M V n) :
    ∃ actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W
          ((completedAdicReduction X d).obj M)).obj (op n), True := by
  have _ := hφ
  have _ := hKplus
  refine ⟨fun U W f n ↦ ?_, trivial⟩
  let B := A ⧸ d.ideal ^ (n + 1)
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let H := finiteCoefficientSliceRestriction X B (completedAdicFiniteCommRing X d n)
    (φ n) V
  let R := ProEtale.localizationRestriction D U.hom U.prop
  let S := finitePerfectAdicScalarModules X d V U W f n
  let P := SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection X d n)
  let O := SheafOfModules.overFunctor.{t + 1} (completedAdicRing X d) W
  let Q := (completedAdicQuotientReduction X d n).obj M
  have : R.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits R := by
    dsimp [R, ProEtale.localizationRestriction]
    infer_instance
  have := (ProEtale.localizationRestrictionLowerStarAdjunction D U.hom U.prop).isLeftAdjoint
  have : PreservesFiniteColimits R := inferInstance
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  have := (completedAdicRestriction_exact X d n).1
  have := (completedAdicRestriction_exact X d n).2
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).1
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.1
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.2
  let c : (H ⋙ R ⋙ S).mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R.mapDerivedCategory ⋙ S.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso H (R ⋙ S) ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryCompIso R S)
  let q : R.mapDerivedCategory.obj (H.mapDerivedCategory.obj Q) ≅
      (ProEtale.upperStar D U.hom).mapDerivedCategory.obj (H.mapDerivedCategory.obj Q) :=
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarIsoLocalizationRestriction D U.hom U.prop)).symm.app _
  let a : S.mapDerivedCategory.obj
      ((localProEtaleComparison U.hom (ULift.{t + 1} B)).obj (K n)) ≅
      O.mapDerivedCategory.obj (P.mapDerivedCategory.obj Q) :=
    S.mapDerivedCategory.mapIso
      ((ProEtale.upperStar D U.hom).mapDerivedCategory.mapIso (e n) ≪≫ q.symm) ≪≫
      (c.app Q).symm ≪≫
      (Functor.mapDerivedCategoryNatIso
        (ordinaryRealizationIso X d φ (compatible_normalized X d φ hcompat)
          V U W f n)).app Q ≪≫
      (Functor.mapDerivedCategoryCompIso P O).app Q
  let Z := (completedAdicReduction X d).obj M
  let E := (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n)
  let z : E.mapDerivedCategory.obj Z ≅
      DerivedCategory.Q.obj ((DerivedCategory.Q.objPreimage Z).asFunctor.obj (op n)) :=
    E.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫
      E.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage Z)
  exact a ≪≫ O.mapDerivedCategory.mapIso
    (((completedAdicFiniteReduction_comparison X d n).some.app M).symm ≪≫ z)

end AlgebraicGeometry.Scheme
