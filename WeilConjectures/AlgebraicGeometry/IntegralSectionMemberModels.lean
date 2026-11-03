/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalIsomorphisms
import WeilConjectures.AlgebraicGeometry.IntegralSectionScalarModels
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
public import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
public import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedRealizationRegularSupplement
public import WeilConjectures.SixFunctors.ContinuousScalarFinitePresentation
public import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # Integral local models on one pro-etale member

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar upperStar lowerStar
  CategoryTheory.Sheaf.monoidalCategory upperStarFromPointComp
  Mod.extendScalarsIsoComapInv laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule continuousScalarFunctor

/-- Pullback to a member admits a finite point model, before any coefficient comparison.
Source: finite constant local models (auxiliary; not a blueprint node). -/
def sectionPointModelAlong
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Y : Scheme.{u}} (f : Y ⟶ S) : Prop :=
  ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
    Mod.IsFinitelyPresented Λ Q ∧
      Nonempty ((CondensedRing.upperStar Λ (f ≫ g)).obj M ≅
        ((upperStarFromPoint Y).mapMod Λ).obj Q)

private def mapRegularCompat {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by
    change (Functor.LaxMonoidal.μ F R R ≫ F.map MonObj.mul) ≫ 𝟙 (F.obj R) =
      F.obj R ◁ 𝟙 (F.obj R) ≫ (Functor.LaxMonoidal.μ F R R ≫ F.map MonObj.mul)
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp])

private def constantRegularIso (A : Type u) [CommRing A] :
    ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A))).obj
        ((FiniteConstantModel.scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A))) ≅
      Mod.regular ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A))) :=
  ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (AddCommGrpCat.of (ULift.{u + 1} A))).mapIso (liftedRegularIso A) ≪≫
      mapRegularCompat
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (AddCommGrpCat.of (ULift.{u + 1} A))

private theorem continuousRegularIso_unit (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Mod.extendUnitHom (FiniteConstantModel.scalarToContinuous A)
      (((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A))).obj
          ((FiniteConstantModel.scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A)))) ≫
      (continuousRegularIso A).hom.hom = FiniteConstantModel.scalarToContinuous A := by
  let φ := FiniteConstantModel.scalarToContinuous A
  have h := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction φ).unit.naturality (constantRegularIso A).hom)
  change (constantRegularIso A).hom.hom ≫ Mod.extendUnitHom φ _ =
    Mod.extendUnitHom φ _ ≫ ((Mod.extendScalars φ).map (constantRegularIso A).hom).hom at h
  dsimp only [continuousRegularIso, id, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
  erw [← Category.assoc, ← h, Category.assoc]
  change (constantRegularIso A).hom.hom ≫
    (Mod.extendUnitHom φ _ ≫ (Mod.extendHom φ (Mod.regularCoefficientMap φ)).hom) = φ
  erw [Mod.extendUnitHom_extendHom]
  change (constantRegularIso A).hom.hom ≫ φ = φ
  change ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (𝟙 _) ≫ 𝟙 _) ≫ φ = φ
  change (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
    (𝟙 (AddCommGrpCat.of (ULift.{u + 1} A))) ≫ φ = φ
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem unitConjugate {C : Type*} [Category* C] {W X Y : C}
    (u : W ⟶ X) (e : X ⟶ Y) (ei : Y ⟶ X) (f : X ⟶ X)
    (he : e ≫ ei = 𝟙 X) :
    (u ≫ e) ≫ (ei ≫ f ≫ e) = (u ≫ f) ≫ e := by
  simp only [Category.assoc]
  rw [← Category.assoc e ei, he, Category.id_comp]

private theorem continuousRegularIso_coefficient (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (f : ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A)) :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map f).hom ≫
        FiniteConstantModel.scalarToContinuous A =
      FiniteConstantModel.scalarToContinuous A ≫
        ((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
          (continuousRegularIso A).hom).hom := by
  let P := (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let φ := FiniteConstantModel.scalarToContinuous A
  let p := P.map ((FiniteConstantModel.scalarModules A).map f)
  have h := congrArg Mod.Hom.hom ((Mod.extendRestrictAdjunction φ).unit.naturality p)
  change p.hom ≫ Mod.extendUnitHom φ _ =
    Mod.extendUnitHom φ _ ≫ ((Mod.extendScalars φ).map p).hom at h
  have h' := congrArg (fun z ↦ z ≫ (continuousRegularIso A).hom.hom) h
  erw [Category.assoc, Category.assoc] at h'
  erw [continuousRegularIso_unit] at h'
  have he := congrArg Mod.Hom.hom (continuousRegularIso A).hom_inv_id
  change (continuousRegularIso A).hom.hom ≫ (continuousRegularIso A).inv.hom = 𝟙 _ at he
  have hh := unitConjugate (Mod.extendUnitHom φ _)
    (continuousRegularIso A).hom.hom (continuousRegularIso A).inv.hom
    ((continuousScalarFunctor A).map f).hom he
  change (Mod.extendUnitHom φ _ ≫ (continuousRegularIso A).hom.hom) ≫
      ((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
        (continuousRegularIso A).hom).hom =
      (Mod.extendUnitHom φ _ ≫ ((Mod.extendScalars φ).map p).hom) ≫
        (continuousRegularIso A).hom.hom at hh
  erw [continuousRegularIso_unit] at hh
  exact h'.trans hh.symm

private def pulledRegularIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ((letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      Mod.regular (AdicCompletion.ring l E X) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact ((upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).mapIso
    (continuousRegularIso (Padic.coefficientExtensionIntegers l E)) ≪≫
      mapRegularCompat (upperStarFromPoint X)
        (DerivedNakayama.integerRing l E)

private theorem pulledRegularIso_coefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (f : ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :
    let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      IntegralModelsStacks.projectionAbSheafify X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      IntegralModelsStacks.projectionCommRingSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let L := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
    FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X ≫
        ((pulledRegularIso l E X).inv ≫ L.map f ≫ (pulledRegularIso l E X).hom).hom =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        ((FiniteConstantModel.scalarModules A).map f).hom ≫
          FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X := by
  let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    IntegralModelsStacks.projectionAbSheafify X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    IntegralModelsStacks.projectionCommRingSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let P := upperStarFromPoint X
  have hc := continuousRegularIso_coefficient A f
  have hn := (constantSchemeIso X).hom.naturality
    ((FiniteConstantModel.scalarModules A).map f).hom
  have hq :
      ((pulledRegularIso l E X).inv ≫
          (continuousScalarFunctor A ⋙ P.mapMod (DerivedNakayama.integerRing l E)).map f ≫
            (pulledRegularIso l E X).hom).hom =
        P.map (((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
          (continuousRegularIso A).hom).hom) := by
    change (𝟙 _ ≫ P.map (continuousRegularIso A).inv.hom) ≫
      P.map ((continuousScalarFunctor A).map f).hom ≫
        (P.map (continuousRegularIso A).hom.hom ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id, Mod.comp_hom', P.map_comp]
  dsimp only
  erw [hq]
  change (constantSchemeIso X).hom.app _ ≫ P.map (FiniteConstantModel.scalarToContinuous A) ≫
      P.map _ = _
  erw [← P.map_comp, ← hc, P.map_comp, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ P.map (FiniteConstantModel.scalarToContinuous A)) hn.symm

private theorem pulledRegularIso_scalar_one (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      IntegralModelsStacks.projectionAbSheafify X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      IntegralModelsStacks.projectionCommRingSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let L := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
    (((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
        (pulledRegularIso l E X).hom).hom).hom.app U
          (1 : (FiniteDiscreteOrdinary.sectionRing A X).obj.obj U) =
      (FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U
            (ULift.up a)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    IntegralModelsStacks.projectionAbSheafify X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    IntegralModelsStacks.projectionCommRingSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let J : GrothendieckTopology X.ProEt := Scheme.ProEt.topology X
  let η := toSheafify J
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
  let c := FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X
  have hc (b : ULift.{u + 1} A) :=
    FiniteDiscreteOrdinary.canonicalRingMap_normalization.{u} A X U b
  have hc1 : c.hom.app U (η.app U (ULift.up 1)) =
      (1 : (FiniteDiscreteOrdinary.sectionRing A X).obj.obj U) := by
    erw [← hc]
    change (FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U 1) = _
    simp only [map_one]
    exact ((FiniteDiscreteOrdinary.canonicalRingMap A X).hom.app U).hom.map_one
  have h := pulledRegularIso_coefficient l E X (scalarEndo A a)
  have h' := congrArg (fun z ↦ z.hom.app U (η.app U (ULift.up 1))) h
  let L := continuousScalarFunctor A ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
  let q := ((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
    (pulledRegularIso l E X).hom).hom
  change q.hom.app U (c.hom.app U (η.app U (ULift.up 1))) =
    c.hom.app U (((constantSheaf J Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom).hom.app U
        (η.app U (ULift.up 1))) at h'
  erw [hc1] at h'
  have hn := congrArg (fun z ↦ z.app U (ULift.up (1 : A)))
    (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom))
  change η.app U (ULift.up (a * 1)) =
    (((constantSheaf J Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom).hom.app U
        (η.app U (ULift.up 1))) at hn
  erw [mul_one] at hn
  erw [← hn, ← hc] at h'
  exact h'

private theorem sectionValueIso_scalar (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let F := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
      integralSectionFunctor l E X ⋙ SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom
    ((sectionValueIso l E X).inv ≫ F.map (scalarEndo A a) ≫
      (sectionValueIso l E X).hom).val.app U
        (1 : (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)).obj.obj U) =
      (Scheme.integralDetailedCoefficientComparison X l E).inv.hom.app U
        ((integralSectionRingIso l E X).hom.hom.app U
          ((FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
            ((Scheme.adicLisseConstantUnit X (ULift.{u + 1} A)).app U (ULift.up a)))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let L := continuousScalarFunctor A ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
  unfold sectionValueIso sectionRegularIso integralSectionFunctor
  let q := ((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
    (pulledRegularIso l E X).hom).hom
  change (Scheme.integralDetailedCoefficientComparison X l E).inv.hom.app U
    ((integralSectionRingIso l E X).hom.hom.app U
      (q.hom.app U ((integralSectionRingIso l E X).inv.hom.app U
        ((Scheme.integralDetailedCoefficientComparison X l E).hom.hom.app U 1)))) = _
  erw [map_one, map_one, pulledRegularIso_scalar_one]
  rfl

private theorem completedRegularIso_scalar (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (a : A) (U : X.ProEtᵒᵖ) :
    let dd : Scheme.ProEtaleAdicCoefficientDatum A :=
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite }
    ((completedRegularIso X d).inv ≫ (Scheme.integralConstantModule X d).map
      (ModuleCat.ofHom (LinearMap.mul A A a)) ≫ (completedRegularIso X d).hom).val.app U
        (1 : (Scheme.pbcAdicCompletion X d).obj.obj U) =
      (Scheme.pbcCompletedComparison X d).hom.hom.app U
        ((Scheme.adicDatumScalar X dd).hom.app U ((Scheme.adicLisseConstantUnit X A).app U a)) :=
    by
  let dd : Scheme.ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  have := Scheme.completedOne_isIso X dd
  let k := asIso (Scheme.completedKoszulOne X dd)
  let : Module ((Scheme.adicDatumRing X dd).obj.obj U)
      (((Scheme.completedKoszulConstant X dd).obj (ModuleCat.of A A)).val.obj U) :=
    (((Scheme.completedKoszulConstant X dd).obj (ModuleCat.of A A)).val.obj U).isModule
  let : Module ((Scheme.adicDatumRing X dd).obj.obj U)
      ((SheafOfModules.unit ((Scheme.adicLisseForget X).obj
        (Scheme.adicDatumRing X dd))).val.obj U) :=
    ((SheafOfModules.unit ((Scheme.adicLisseForget X).obj
      (Scheme.adicDatumRing X dd))).val.obj U).isModule
  unfold completedRegularIso Scheme.integralConstantModule
  change (Scheme.pbcCompletedComparison X d).hom.hom.app U
    (k.inv.val.app U (((Scheme.completedKoszulConstant X dd).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (k.hom.val.app U ((Scheme.pbcCompletedComparison X d).inv.hom.app U 1)))) = _
  erw [map_one]
  erw [Scheme.completedOne_scalar X dd a U]
  erw [map_smul]
  have hk := congrArg (fun f ↦ f.val.app U (1 : (Scheme.adicDatumRing X dd).obj.obj U))
    k.hom_inv_id
  change k.inv.val.app U ((Scheme.completedKoszulOne X dd).val.app U
    (1 : (Scheme.adicDatumRing X dd).obj.obj U)) =
      (1 : (Scheme.adicDatumRing X dd).obj.obj U) at hk
  erw [hk]
  change (Scheme.pbcCompletedComparison X d).hom.hom.app U (_ * 1) = _
  erw [mul_one]

private theorem constantValueIso_scalar (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
      { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
    let G := ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom ⋙
      Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
    ((constantValueIso l E X).inv ≫
      G.map (scalarEndo (Padic.coefficientExtensionIntegers l E) a) ≫
        (constantValueIso l E X).hom).val.app U
          (1 : (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)).obj.obj U) =
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom.hom.app U
        ((Scheme.adicDatumScalar X dd).hom.app U
          ((Scheme.adicLisseConstantUnit X (Scheme.PbcIntegralRing l E)).app U (ULift.up a))) :=
    by
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let d := Scheme.pbcIntegralDatum l E
  let G := Scheme.integralConstantModule X d
  let H := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom
  have h : (completedInputIso l E).inv ≫ H.map (scalarEndo A a) ≫
      (completedInputIso l E).hom =
    ModuleCat.ofHom (LinearMap.mul (Scheme.PbcIntegralRing l E)
      (Scheme.PbcIntegralRing l E) (ULift.up a)) := by
    rfl
  have he : (constantValueIso l E X).inv ≫ (H ⋙ G).map (scalarEndo A a) ≫
      (constantValueIso l E X).hom =
    (completedRegularIso X d).inv ≫
      G.map (ModuleCat.ofHom (LinearMap.mul (Scheme.PbcIntegralRing l E)
        (Scheme.PbcIntegralRing l E) (ULift.up a))) ≫ (completedRegularIso X d).hom := by
    dsimp only [constantValueIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.comp_map]
    change (completedRegularIso X d).inv ≫ G.map (completedInputIso l E).inv ≫
      G.map (H.map (scalarEndo A a)) ≫ G.map (completedInputIso l E).hom ≫
        (completedRegularIso X d).hom = _
    erw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, h]
  dsimp only
  change (((constantValueIso l E X).inv ≫ (H ⋙ G).map (scalarEndo A a) ≫
    (constantValueIso l E X).hom).val.app U) _ = _
  erw [he]
  exact completedRegularIso_scalar X d (ULift.up a) U

private theorem scalarToContinuous_pointComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     FiniteConstantModel.scalarToContinuous (Padic.coefficientExtensionIntegers l E)) ≫
      (IntegralConstantModel.pointComparison l E).hom.hom =
    (letI := spectralNorm.normedField (Padic l) E
     FiniteConstantModel.scalarToContinuous (Padic.coefficientExtensionIntegers l E)) := by
  erw [IntegralModelsStacks.pointComparison_eq]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (coherentTopology Profinite.{u}) _ _
    (sfbCondensedIntegers l E).X.property
  change _ ≫ (_ ≫ _) = _ ≫ _
  erw [← Category.assoc]
  erw [scalarToContinuous_unit, scalarToContinuous_unit]
  ext S a
  rfl

private theorem canonicalAbelianMap_pointComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     FiniteDiscreteOrdinary.canonicalAbelianMap.{u} (Padic.coefficientExtensionIntegers l E) X) ≫
      (upperStarFromPoint X).map (IntegralConstantModel.pointComparison l E).hom.hom =
    (IntegralModelsStacks.discreteCoefficientAbelianIso X
      (Padic.coefficientExtensionIntegers l E)).hom ≫ IntegralModelsStacks.scalarMap l E X := by
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let P := upperStarFromPoint X
  have hd := (letI := spectralNorm.normedField (Padic l) E
    IntegralModelsStacks.pointConstantAbIso_scalar A)
  have hp := scalarToContinuous_pointComparison l E
  let φ := (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    FiniteConstantModel.scalarToContinuous A)
  let j := (IntegralModelsStacks.pointConstantAbIso A).hom
  let ψ := (letI := spectralNorm.normedField (Padic l) E
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (IntegralModelsStacks.constantToContinuous A))
  let C := (constantSchemeIso X).hom.app (AddCommGrpCat.of (ULift.{u + 1} A))
  change (C ≫ P.map φ) ≫ P.map (IntegralConstantModel.pointComparison l E).hom.hom =
    (C ≫ P.map j) ≫ P.map ψ
  have h1 : (C ≫ P.map φ) ≫ P.map (IntegralConstantModel.pointComparison l E).hom.hom =
      C ≫ P.map (φ ≫ (IntegralConstantModel.pointComparison l E).hom.hom) := by
    exact (Category.assoc C (P.map φ)
      (P.map (IntegralConstantModel.pointComparison l E).hom.hom)).trans
      (congrArg (fun z ↦ C ≫ z)
        (P.map_comp φ (IntegralConstantModel.pointComparison l E).hom.hom).symm)
  have h2 := congrArg (fun z ↦ C ≫ P.map z) (hp.trans hd.symm)
  have h3 : C ≫ P.map (j ≫ ψ) = (C ≫ P.map j) ≫ P.map ψ :=
    (congrArg (fun z ↦ C ≫ z) (P.map_comp j ψ)).trans
      (Category.assoc C (P.map j) (P.map ψ)).symm
  exact h1.trans (h2.trans h3)

private theorem cancelIsoChain {C : Type*} [Category* C]
    {V W X Y Z T : C} (a : W ≅ X) (b : X ≅ Y) (c : Z ≅ Y) (d : Z ≅ T)
    (f : V ⟶ Z) (g : V ⟶ W)
    (h : (f ≫ d.hom) ≫ (a ≪≫ b ≪≫ c.symm ≪≫ d).inv = g) :
    f ≫ c.hom ≫ b.inv = g ≫ a.hom := by
  have hh := congrArg (fun z ↦ z ≫ a.hom) h
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh

private theorem coefficientRingCompatibility (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      IntegralModelsStacks.projectionAbSheafify X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      IntegralModelsStacks.projectionCommRingSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
      { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
    FiniteDiscreteOrdinary.canonicalRingMap.{u} (Padic.coefficientExtensionIntegers l E) X ≫
        (integralSectionRingIso l E X).hom ≫ (WeilConjectures.purCoefficientIso l E X).inv =
      Scheme.adicDatumScalar X dd ≫ (Scheme.pbcCompletedComparison X
        (Scheme.pbcIntegralDatum l E)).hom := by
  let : EssentiallySmall.{u + 1} X.ProEt := IntegralModelsStacks.projectionSiteSmall X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    IntegralModelsStacks.projectionAbSheafify X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    IntegralModelsStacks.projectionCommRingSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let J : GrothendieckTopology X.ProEt := Scheme.ProEt.topology X
  let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
    { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
      quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
  obtain ⟨c, _, _⟩ := IntegralModelsStacks.integral_constant_section_projection l E X
  have hc : c.integers.hom ≫ IntegralModelsStacks.sectionMap X
        (IntegralModelsStacks.scalarMap l E X) ≫
          (IntegralModelsStacks.completedSectionIso l E X).inv =
      Scheme.adicDatumScalar X dd := by
    apply limit.hom_ext
    intro n
    exact (c.projection n.unop).trans
      ((Scheme.adicDatumScalar_exists X dd).exists.choose_spec n.unop).symm
  have ha : FiniteDiscreteOrdinary.canonicalRingMap.{u} A X ≫
      (IntegralModelsStacks.pointSectionIso l E X).hom =
        c.integers.hom ≫ IntegralModelsStacks.sectionMap X
          (IntegralModelsStacks.scalarMap l E X) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      (InternalAbelianSheafModule.sectionRingSheaf J
        (condensedRingObj (IntegralModelsStacks.integersObj l E) X)).property
    ext U a
    change (IntegralModelsStacks.pointSectionIso l E X).hom.hom.app U
      ((FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U a)) =
      (IntegralModelsStacks.scalarMap l E X).hom.app U
        (c.integers.hom.hom.app U
          ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app U a))
    erw [FiniteDiscreteOrdinary.canonicalRingMap_normalization, c.integers_normalized]
    exact congrArg (fun z ↦ z.hom.app U
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a))
      (canonicalAbelianMap_pointComparison l E X)
  have hh : (FiniteDiscreteOrdinary.canonicalRingMap A X ≫
        (IntegralModelsStacks.pointSectionIso l E X).hom) ≫
        (IntegralModelsStacks.completedSectionIso l E X).inv =
      Scheme.adicDatumScalar X dd :=
    ((congrArg (fun z ↦ z ≫ (IntegralModelsStacks.completedSectionIso l E X).inv) ha).trans
      (Category.assoc _ _ _)).trans hc
  exact cancelIsoChain
    (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E))
    (WeilConjectures.purCoefficientIso l E X) (integralSectionRingIso l E X)
    (IntegralModelsStacks.pointSectionIso l E X)
    (FiniteDiscreteOrdinary.canonicalRingMap A X) (Scheme.adicDatumScalar X dd) hh

/--
The two fixed scalar realizations agree on the lifted regular module and on every
endomorphism given by multiplication by a scalar. This is the rank-one coefficient
calculation: the normalized section-ring and completed-coefficient projections agree
on the scalar section, and the completion projections are jointly monic.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the regular
scalar calculation in the integral constructibility bridge.
Proof: identify both regular values with the sectionwise unit module using the
constant-sheaf, scalar-extension, point-pullback, section-action, and coefficient
restriction unit maps. For a scalar `a`, naturality of each unit map identifies its
image with multiplication by the corresponding constant section. The fixed
projection formulas agree at every positive quotient, hence the completion
projections identify the two maps. The zero scalar and empty scheme are included.
(blueprint: lem-sfb-integral-section-regular-scalars-scalar).
-/
private theorem scalarComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let A := Padic.coefficientExtensionIntegers l E
    let R := ModuleCat.of A (ULift.{u + 1} A)
    let F :=
      (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
       continuousScalarFunctor A) ⋙
        (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
        integralSectionFunctor l E X ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (Scheme.integralDetailedCoefficientComparison X l E).hom
    let G :=
      ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom ⋙
      Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
    ∃ e : F.obj R ≅ G.obj R,
      ∀ a : A,
        F.map (ModuleCat.ofHom ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
          ((LinearMap.mulLeft A a).comp
            (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))) ≫ e.hom =
          e.hom ≫ G.map (ModuleCat.ofHom
            ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
              ((LinearMap.mulLeft A a).comp
                (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))) := by
  let eF := sectionValueIso l E X
  let eG := constantValueIso l E X
  refine ⟨eF ≪≫ eG.symm, ?_⟩
  intro a
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let F :=
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     continuousScalarFunctor A) ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
      integralSectionFunctor l E X ⋙ SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom
  let G := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom ⋙
    Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
  have h : eF.inv ≫ F.map (scalarEndo A a) ≫ eF.hom =
      eG.inv ≫ G.map (scalarEndo A a) ≫ eG.hom := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (sectionValueIso_scalar l E X a U).trans
      ((coefficientScalarCompatibility l E X a U).trans
        (constantValueIso_scalar l E X a U).symm)
  change F.map (scalarEndo A a) ≫ (eF.hom ≫ eG.inv) =
    (eF.hom ≫ eG.inv) ≫ G.map (scalarEndo A a)
  have h' := congrArg (fun z ↦ eF.hom ≫ z ≫ eG.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h'

/-- The specified continuous-scalar, point-pullback and section-action composite.
Source: Bhatt--Scholze, Proposition 6.8.11(3), integral scalar models
(blueprint: lem-sfb-integral-section-regular-scalars). -/
@[irreducible] private def sectionRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) :=
  (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
   continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
    integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom

/-- The specified completed-constant realization with the recorded scalar universe change.
Source: Bhatt--Scholze, Proposition 6.8.11(3), integral scalar models
(blueprint: lem-sfb-integral-section-regular-scalars). -/
@[irreducible] private def completedRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) :=
  ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
      Padic.coefficientExtensionIntegers l E).toRingHom ⋙
    Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)

/-- The two fixed scalar realizations agree on the lifted regular module, compatibly
with every scalar endomorphism. This is a rank-one coefficient calculation; no finite
presentation, cokernel or arbitrary module is involved.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the regular scalar
calculation in the integral constructibility bridge
(blueprint: lem-sfb-integral-section-regular-scalars).

Proof: constant sheafification sends the regular scalar module to the regular constant
coefficient module. Scalar extension sends it to the regular continuous coefficient
module by its adjunction, and point inverse image sends it to the regular pulled-back
coefficient module. Section action identifies this with the unit section module;
restriction along the prescribed ring isomorphisms identifies it with the completed
coefficient unit. On the completed-constant side, sheafification and scalar extension
likewise identify the lifted regular module with that same unit. These give the desired
isomorphism. A linear endomorphism of the lifted regular module is multiplication by
its value on the lifted element 1. On each positive uniformizer quotient the normalized
section-ring comparison and the normalized detailed comparison send this element to
its constant section. The constant completion map has the identical quotient formula.
The completion projections are jointly monic, so these scalar sections agree before
reduction. Naturality of scalar extension's unit and the point-pullback unit then
identifies the two endomorphisms of the unit module. This proves the displayed square.
The zero scalar and the empty scheme require no exception. -/
private theorem regularComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ e : (sectionRealization l E X).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      (completedRealization l E X).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))),
      ∀ f : ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)),
        (sectionRealization l E X).map f ≫ e.hom =
          e.hom ≫ (completedRealization l E X).map f := by
  unfold sectionRealization completedRealization
  obtain ⟨e, he⟩ := scalarComparison l E X
  refine ⟨e, ?_⟩
  intro f
  let a := (f.hom (ULift.up 1)).down
  have hfa : f = scalarEndomorphism _ a := endomorphism_eq_scalar _ f
  rw [hfa]
  exact he a

/-- The explicit scalar model in the localized module category.
Source: the completed scalar model (auxiliary; not a blueprint node). -/
def integralSectionMemberModel (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M : AdicCompletion.Modules l E X) : Prop :=
  ∃ N : ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E),
    Module.FinitePresentation (Scheme.PbcIntegralRing l E) N ∧
      Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj M))) ≅
          (SheafOfModules.overFunctor _ U).obj
            ((Scheme.proEtaleModuleInverseImage g
              (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                ((Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj N)))

@[irreducible] private noncomputable def pointModelFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (upperStarFromPoint X).mapMod Λ

private theorem sectionPointModelAlong_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Y : Scheme.{u}} (f : Y ⟶ S) :
    sectionPointModelAlong Λ g M f ↔
      ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ Q ∧
        Nonempty ((CondensedRing.upperStar Λ (f ≫ g)).obj M ≅
          (pointModelFunctor Λ Y).obj Q) := by
  unfold pointModelFunctor
  rfl

private theorem pointModelPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      ((pointModelFunctor Λ X).obj Q) ≅
      (pointModelFunctor Λ Y).obj Q) := by
  let fixedAbSheafify (T : Scheme.{u}) :
      HasSheafify (Scheme.ProEt.topology T) Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, u} T
  let fixedSiteSmall (T : Scheme.{u}) :
      EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let c : (upperStarFromPoint X).mapMod Λ ⋙ CondensedRing.upperStar Λ f ≅
      (upperStarFromPoint Y).mapMod Λ := by
    unfold CondensedRing.upperStar
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapModCompIso (upperStarFromPoint X) (ProEtale.upperStar Ab.{u + 1} f)
          (upperStarFromPointComp f).hom Λ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
          (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
      Functor.rightUnitor _
  unfold pointModelFunctor
  exact ⟨c.app Q⟩

@[irreducible] private noncomputable def integralMemberPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    AdicCompletion.Modules l E X ⥤ AdicCompletion.Modules l E Y :=
  CondensedRing.upperStar (DerivedNakayama.integerRing l E) f

@[irreducible] private noncomputable def integralPointModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E) ⥤ AdicCompletion.Modules l E X :=
  pointModelFunctor (DerivedNakayama.integerRing l E) X

private theorem nativePointModel_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Y : Scheme.{u}} (g : S ⟶ X) (f : Y ⟶ S)
    (M : AdicCompletion.Modules l E X) :
    sectionPointModelAlong (DerivedNakayama.integerRing l E) g M f ↔
      ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E),
        Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) Q ∧
        Nonempty ((integralMemberPullback l E (f ≫ g)).obj M ≅
          (integralPointModel l E Y).obj Q) := by
  unfold integralMemberPullback integralPointModel
  exact sectionPointModelAlong_iff (DerivedNakayama.integerRing l E) g M f

private theorem nativePointModelPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E)) :
    Nonempty ((integralMemberPullback l E f).obj
      ((integralPointModel l E X).obj Q) ≅ (integralPointModel l E Y).obj Q) := by
  unfold integralMemberPullback integralPointModel
  exact pointModelPullback (DerivedNakayama.integerRing l E) f Q

private theorem nativeLocalIsomorphisms (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M N : AdicCompletion.Modules l E X) :
    Nonempty ((integralMemberPullback l E
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj M ≅
      (integralMemberPullback l E
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj N) ↔
    Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj M))) ≅
      (SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj N)))) := by
  unfold integralMemberPullback
  exact integralSectionLocalIsomorphisms l E g U M N

private theorem finitePresentation_restrict
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (N : ModuleCat.{u + 1} S)
    (hN : Module.FinitePresentation S N) :
    Module.FinitePresentation R ((ModuleCat.restrictScalars e.toRingHom).obj N) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hbij : Function.Bijective (Algebra.linearMap R S) := e.bijective
  let : Module.FinitePresentation R S := Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective (Algebra.linearMap R S) hbij)
  let N' := (ModuleCat.restrictScalars e.toRingHom).obj N
  let : Module S N' := N.isModule
  let : Module.FinitePresentation S N' := hN
  let : IsScalarTower R S N' :=
    { smul_assoc := fun r s x ↦ by
        change (e r * s) • x = e r • (s • x)
        exact mul_smul (e r) s x }
  exact Module.FinitePresentation.trans R N' S

@[irreducible] private noncomputable def integralPointScalarFunctor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E) :=
  let A := Padic.coefficientExtensionIntegers l E
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousScalarFunctor A

private theorem integerClassification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∀ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) Q ↔
      ∃ N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E),
        Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N ∧
        Nonempty (Q ≅ (integralPointScalarFunctor l E).obj N) := by
  unfold integralPointScalarFunctor
  let A := Padic.coefficientExtensionIntegers l E
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact continuousScalarFinitePresentation A

-- Preserve the established comparison while this consumer awaits its own assigned
-- condensed route switch. This is the original argument, with only a private name.

/-- The fixed integral section comparison sends a finitely presented ordinary scalar
module, extended from the condensed point, to its completed constant realization.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the scalar
comparison in the integral constructibility bridge.
(blueprint: lem-sfb-integral-section-scalar-models).

Proof: choose a finite presentation of N by free scalar modules. The two realizations
preserve finite sums and cokernels: constant sheafification, extension of scalars,
and inverse image do, and section comparison and coefficient restriction are
equivalences. On the regular scalar module identify both values with the coefficient
module. At every positive uniformizer quotient, the prescribed coefficient maps send
an element to its constant section. Joint monicity of the completion projections
identifies the resulting maps on the completed regular module. This identification
commutes with scalar endomorphisms: evaluation of a constant function at the singleton
returns that scalar. The ULift change sends a lifted scalar to the same element.
Extend the regular-module comparison to the finite free terms by biproducts. Checking
each matrix entry identifies the two presentation maps. Preservation of their
cokernels and cokernel uniqueness give the asserted isomorphism on N. Empty matrices,
torsion modules and empty schemes are included. -/
private theorem integralSectionScalarModels_legacy (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (hN : Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N) :
    Nonempty ((SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
      ((integralSectionFunctor l E X).obj
        (((upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).obj
          ((let A := Padic.coefficientExtensionIntegers l E
            letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
            continuousScalarFunctor A).obj N))) ≅
      (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj
        ((ModuleCat.restrictScalars
          (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom).obj N)) := by
  have hF := (finiteColimits l E X).1
  have hG := (finiteColimits l E X).2
  have haF : (sectionRealization l E X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ hF
  have haG : (completedRealization l E X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ hG
  obtain ⟨e, he⟩ := regularComparison l E X
  have h := scalarPresentationComparison
    (sectionRealization l E X)
    (completedRealization l E X) e he N hN
  unfold sectionRealization
    completedRealization at h
  exact h

private theorem scalarModelComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (hN : Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N) :
    Nonempty ((SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
      ((integralSectionFunctor l E X).obj
        ((integralPointModel l E X).obj
          ((integralPointScalarFunctor l E).obj N))) ≅
      (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj
        ((ModuleCat.restrictScalars
          (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom).obj N)) := by
  unfold integralPointScalarFunctor integralPointModel pointModelFunctor
  exact integralSectionScalarModels l E X N hN

private theorem mapNonemptyIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (h : Nonempty (M ≅ N)) :
    Nonempty (F.obj M ≅ F.obj N) := by
  obtain ⟨a⟩ := h
  exact ⟨F.mapIso a⟩

private theorem transNonemptyIso {C : Type*} [Category C] {M N P : C}
    (h : Nonempty (M ≅ N)) (k : Nonempty (N ≅ P)) : Nonempty (M ≅ P) := by
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := k
  exact ⟨a ≪≫ b⟩

private theorem symmNonemptyIso {C : Type*} [Category C] {M N : C}
    (h : Nonempty (M ≅ N)) : Nonempty (N ≅ M) := by
  obtain ⟨a⟩ := h
  exact ⟨a.symm⟩

/-- On a single member, the fixed section comparison preserves finite scalar models.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), scalar comparison
in step 7 of the integral constructibility bridge.
(auxiliary; not a blueprint node).

Proof: write a finite presentation of the point module as a matrix between finite sums
of the regular module. Evaluation of continuous scalar functions at the singleton
identifies the matrix entries with the valuation ring underlying PbcIntegralRing.
Form the ordinary cokernel N of this matrix. Pullback from the point, the section-action
equivalence, and restriction along the coefficient isomorphism preserve finite sums and
cokernels. On every positive quotient the normalized coefficient comparisons send each
entry to the same constant scalar section; joint monicity of the limit projections
identifies the completed entries. Naturality of those projections also identifies the
coefficient maps after inverse image along g and restriction to U. Hence the localized
finite cokernel is the completed constant realization of N. Conversely choose a finite
presentation of N and form its matrix cokernel of regular modules on the condensed point.
It is finitely presented by construction. The same comparison and full faithfulness of
the section-action and localized-site equivalences reflect the local isomorphism to
that point model. This is one member only: no cover, stratification or Noetherianity
occurs. Empty matrices, torsion and empty schemes are allowed. -/
theorem integralSectionMemberModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M : AdicCompletion.Modules l E X) :
    sectionPointModelAlong (DerivedNakayama.integerRing l E) g M U.hom ↔
      integralSectionMemberModel l E g U M := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let e : Scheme.PbcIntegralRing l E ≃+* A := ULift.ringEquiv
  constructor
  · intro h
    obtain ⟨Q, hQ, b⟩ := (nativePointModel_iff l E g U.hom M).mp h
    obtain ⟨N, hN, c⟩ := (integerClassification l E Q).mp hQ
    have d := transNonemptyIso b
      (transNonemptyIso
        (mapNonemptyIso
          (integralPointModel l E ((𝟭 Scheme).obj U.left)) c)
        (symmNonemptyIso (nativePointModelPullback l E
          (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)
          ((integralPointScalarFunctor l E).obj N))))
    have d' := (nativeLocalIsomorphisms l E g U M
      ((integralPointModel l E X).obj ((integralPointScalarFunctor l E).obj N))).mp d
    have a := scalarModelComparison l E X N hN
    have a' := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) a)
    refine ⟨(ModuleCat.restrictScalars
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom).obj N, ?_,
      transNonemptyIso d' a'⟩
    exact finitePresentation_restrict e N hN
  · rintro ⟨N, hN, b⟩
    let N' := (ModuleCat.restrictScalars e.symm.toRingHom).obj N
    have hN' : Module.FinitePresentation A N' :=
      finitePresentation_restrict e.symm N hN
    have a := scalarModelComparison l E X N' hN'
    have a' := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) a)
    have roundtrip : (ModuleCat.restrictScalars
        (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
          Padic.coefficientExtensionIntegers l E).toRingHom).obj N' ≅ N :=
      (ModuleCat.restrictScalarsComp'App e.toRingHom e.symm.toRingHom
        (RingHom.id _) e.symm_toRingHom_comp_toRingHom.symm N).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl N
    have r := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)))
          (mapNonemptyIso
            (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E))
            ⟨roundtrip.symm⟩))
    have d := transNonemptyIso (transNonemptyIso b r) (symmNonemptyIso a')
    have d' := (nativeLocalIsomorphisms l E g U M
      ((integralPointModel l E X).obj ((integralPointScalarFunctor l E).obj N'))).mpr d
    apply (nativePointModel_iff l E g U.hom M).mpr
    refine ⟨(integralPointScalarFunctor l E).obj N', ?_, transNonemptyIso d'
      (nativePointModelPullback l E
          (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)
          ((integralPointScalarFunctor l E).obj N'))⟩
    exact (integerClassification l E ((integralPointScalarFunctor l E).obj N')).mpr
      ⟨N', hN', ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
