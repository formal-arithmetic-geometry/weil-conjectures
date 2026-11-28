/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualModulePullCompUnit
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationLift
import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationMap
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullComputation

/-! # Completed composition and descent to all raw rational fraction arrows.

The ordinary rational comparisons of composable pullbacks compose
(`rationalOrdinaryComparison_comp`): on K-flat complexes with flat terms every derived functor
is computed termwise, and the termwise maps agree on unit generators
(`rationalModuleComparison_comp`). Inverting the completed-pullback units then gives the
composition of the realization comparisons and of the raw rational pullbacks.

## Implementation details

The module hypotheses restrict generators along `MorphismProperty.Over.pullbackComp` through
`PresheafOfModules.restrictₛₗ`: the semilinear view exposes the target carrier without unfolding
chart rings, which keeps elaborating these statements cheap.

## References

* Bhatt--Scholze, Remark 6.8.15, p. 62
* Stacks Tags 03CB, 0D6D, 07A4, 099N
* Stacks Tags 099N, 099J, 0A0E, 0B65 and 0DV0
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

omit [IsNoetherian Z] [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))] in
/-- The raw pullback of a comparison sends a localized integral morphism to the localization
of its completed pullback. -/
theorem RationalRealizationPullbackComparison.rawPull_map_rationalization {g : X ⟶ Y}
    {sX : RationalModuleRealization l E X} {sY : RationalModuleRealization l E Y}
    (a : RationalRealizationPullbackComparison l E g sX sY)
    {K L : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)} (f : K ⟶ L) :
    a.rawPull.map ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (a.raw_objects K) ≫
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((a.integral.completedFunctor l E).map f) ≫ eqToHom (a.raw_objects L).symm := by
  have h := a.raw_fractions K L f 0
  simpa only [rationalPullFraction, pow_zero, one_smul] using h

omit [IsNoetherian Z] [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))] in
/-- The realization comparison of a pullback on a localized integral object, expressed through
the ordinary comparison and the inverse of the completed-pullback unit. -/
theorem RationalRealizationPullbackComparison.alpha_hom_app {g : X ⟶ Y}
    {sX : RationalModuleRealization l E X} {sY : RationalModuleRealization l E Y}
    (a : RationalRealizationPullbackComparison l E g sX sY)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    a.alpha.hom.app ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      sX.J.map (eqToHom (a.raw_objects K)) ≫
        eqToHom (sX.objects ((a.integral.completedFunctor l E).obj K)) ≫
        (haveI := a.integral.unit_isIso K
         inv ((pbcDerivedExtend (rationalPullScalar l E sX)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj))) ≫
        a.ordinaryComparison.hom.app K.obj ≫
        (rationalPullDerived l E g a.rationalCoefficient).map (eqToHom (sY.objects K).symm) := by
  have := a.integral.unit_isIso K
  rw [← a.alpha_normalization K]
  simp

omit [Fact l.Prime] in
private theorem rationalCompleted_app_eq_eqToHom {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {A B : C} (e : A = B) :
    α.app A = F.map (eqToHom e) ≫ α.app B ≫ G.map (eqToHom e.symm) := by
  subst e
  simp

omit [Fact l.Prime] in
/-- A comparison of composite targets obtained by inverting units is natural. -/
private theorem rationalCompletedComp_naturality {C D T : Type*} [Category C] [Category D]
    [Category T] {Dg Sg : C ⥤ D} {Dh Sh : D ⥤ T} {Dc Sc : C ⥤ T}
    (ug : Dg ⟶ Sg) (uh : Dh ⟶ Sh) (uc : Dc ⟶ Sc) (c : Dg ⋙ Dh ⟶ Dc) {K L : C}
    (f : K ⟶ L)
    {φK : Sh.obj (Sg.obj K) ⟶ Sc.obj K} {φL : Sh.obj (Sg.obj L) ⟶ Sc.obj L}
    (hK : Dh.map (ug.app K) ≫ uh.app (Sg.obj K) ≫ φK = c.app K ≫ uc.app K)
    (hL : Dh.map (ug.app L) ≫ uh.app (Sg.obj L) ≫ φL = c.app L ≫ uc.app L)
    [IsIso (Dh.map (ug.app K) ≫ uh.app (Sg.obj K))] :
    Sh.map (Sg.map f) ≫ φL = φK ≫ Sc.map f := by
  rw [← cancel_epi (Dh.map (ug.app K) ≫ uh.app (Sg.obj K))]
  have nh := uh.naturality (Sg.map f)
  have ng := ug.naturality f
  have nc := c.naturality f
  have nu := uc.naturality f
  simp only [Functor.comp_map] at nc
  rw [Category.assoc, ← reassoc_of% nh, ← Functor.map_comp_assoc, ← ng,
    Functor.map_comp_assoc, hL, Category.assoc, reassoc_of% hK, ← nu, ← reassoc_of% nc]

omit [Fact l.Prime] in
private theorem rationalOrdinary_app_eq_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {A B : C} (i : A ≅ B) :
    α.app B = F.map i.inv ≫ α.app A ≫ G.map i.hom := by
  simp

/-- The balanced flattenings of composable pullbacks compose: on every integral module, the
flattening of the composite agrees with the pasting of the two flattenings, the ordinary
pullback compositor and the rational module compositor. -/
theorem rationalModuleComparison_comp (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient ≅
        rationalPullModule l E (h ≫ g) ac.rationalCoefficient)
    (hmodule : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V)),
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (rationalCoherenceUnit l E h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (rationalCoherenceUnit l E g ag.rationalCoefficient M V m)) =
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (rationalCoherenceUnit l E (h ≫ g) ac.rationalCoefficient M V m))
    (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :
    (pbcExtend (rationalPullScalar l E sZ)).map
        ((pbcActualModulePullCompIso h g (pbcIntegralDatum l E)).inv.app M) ≫
      ac.moduleComparison.hom.app M =
    ah.moduleComparison.hom.app ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M) ≫
      (rationalPullModule l E h ah.rationalCoefficient).map
        (ag.moduleComparison.hom.app M) ≫
      moduleComp.hom.app ((pbcExtend (rationalPullScalar l E sX)).obj M) := by
  have hcu {S T : Scheme.{u}} (f : S ⟶ T)
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
      (N : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEt)
      (n : N.val.obj (op V)) :
      pbcTensorSection c
        ((proEtaleRingModulePullback f (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj N)
        (op ((proEtaleBaseChange f).obj V)) 1
        (proEtaleRingModuleUnitSection f (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _) N V n) =
        rationalCoherenceUnit l E f c N V n := by
    unfold rationalCoherenceUnit
    rfl
  let d := pbcIntegralDatum l E
  apply ((((pbcActualModuleAdjunction g d).comp (pbcActualModuleAdjunction h d)).comp
    (pbcScalarAdjunction (rationalPullScalar l E sZ))).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨V⟩ := V
  ext m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hau {S T : Scheme.{u}} (f : S ⟶ T) (N : pbcModules T (pbcAdicCompletion T d))
      (U : T.ProEt) (y : N.val.obj (op U)) :
      ((pbcActualModuleAdjunction f d).unit.app N).val.app (op U) y =
        pbcActualModuleUnitSection f d N U y :=
    (pbcActualModuleAdjunction_exists f d).exists.choose_spec N U y
  have hu : (((((pbcActualModuleAdjunction g d).comp (pbcActualModuleAdjunction h d)).comp
      (pbcScalarAdjunction (rationalPullScalar l E sZ))).unit.app M).val.app (op V) m) =
      pbcTensorSection (rationalPullScalar l E sZ)
        ((pbcActualModulePull h d).obj ((pbcActualModulePull g d).obj M))
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) 1
        (pbcActualModuleUnitSection h d ((pbcActualModulePull g d).obj M)
          ((proEtaleBaseChange g).obj V) (pbcActualModuleUnitSection g d M V m)) := by
    simp only [Adjunction.comp_unit_app]
    change ((pbcScalarAdjunction (rationalPullScalar l E sZ)).unit.app
        ((pbcActualModulePull h d).obj ((pbcActualModulePull g d).obj M))).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (((pbcActualModuleAdjunction h d).unit.app ((pbcActualModulePull g d).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((pbcActualModuleAdjunction g d).unit.app M).val.app (op V) m)) = _
    simp only [hau, WeilConjectures.FdIntegralScalarForward.pbcScalarAdjunction_unit]
  change ((pbcExtend (rationalPullScalar l E sZ)).map
        ((pbcActualModulePullCompIso h g d).inv.app M) ≫
      ac.moduleComparison.hom.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (((((pbcActualModuleAdjunction g d).comp (pbcActualModuleAdjunction h d)).comp
        (pbcScalarAdjunction (rationalPullScalar l E sZ))).unit.app M).val.app (op V) m) =
    (ah.moduleComparison.hom.app ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M) ≫
      (rationalPullModule l E h ah.rationalCoefficient).map
        (ag.moduleComparison.hom.app M) ≫
      moduleComp.hom.app ((pbcExtend (rationalPullScalar l E sX)).obj M)).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (((((pbcActualModuleAdjunction g d).comp (pbcActualModuleAdjunction h d)).comp
        (pbcScalarAdjunction (rationalPullScalar l E sZ))).unit.app M).val.app (op V) m)
  rw [hu]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [WeilConjectures.FdIntegralScalarForward.pbcTensor_map]
  erw [pbcActualModulePullCompIso_inv_app_unit]
  erw [← pbcTensorSection_restrict]
  erw [PresheafOfModules.naturality_apply]
  erw [ac.module_unit]
  rw [hcu (h ≫ g) ac.rationalCoefficient ((pbcExtend (rationalPullScalar l E sX)).obj M) V
    (pbcTensorSection (rationalPullScalar l E sX) M (op V) 1 m)]
  erw [ah.module_unit ((pbcActualModulePull g d).obj M) ((proEtaleBaseChange g).obj V)
    (pbcActualModuleUnitSection g d M V m)]
  rw [hcu h ah.rationalCoefficient
    ((pbcExtend (rationalPullScalar l E sY)).obj ((pbcActualModulePull g d).obj M))
    ((proEtaleBaseChange g).obj V)
    (pbcTensorSection (rationalPullScalar l E sY) ((pbcActualModulePull g d).obj M)
      (op ((proEtaleBaseChange g).obj V)) 1 (pbcActualModuleUnitSection g d M V m))]
  erw [rationalPullModule_map_unit]
  erw [ag.module_unit M V m]
  rw [hcu g ag.rationalCoefficient ((pbcExtend (rationalPullScalar l E sX)).obj M) V
    (pbcTensorSection (rationalPullScalar l E sX) M (op V) 1 m)]
  exact (hmodule ((pbcExtend (rationalPullScalar l E sX)).obj M) V
    (pbcTensorSection (rationalPullScalar l E sX) M (op V) 1 m)).symm

/-- The composition coherence of the ordinary rational comparisons on a K-flat complex with
flat terms, where every derived functor is computed termwise. -/
private theorem rationalOrdinaryComparison_comp_Q (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient ≅
        rationalPullModule l E (h ≫ g) ac.rationalCoefficient)
    (hmodule : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V)),
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (rationalCoherenceUnit l E h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (rationalCoherenceUnit l E g ag.rationalCoefficient M V m)) =
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (rationalCoherenceUnit l E (h ≫ g) ac.rationalCoefficient M V m))
    (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient ≅
        rationalPullDerived l E (h ≫ g) ac.rationalCoefficient)
    (hderived : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
      ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
          rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
        (rationalPullDerived l E h ah.rationalCoefficient).map
            (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
          rationalPullComplexCounit l E h ah.rationalCoefficient
            (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P))
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion X (pbcIntegralDatum l E)) P)
    (hf' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion X (pbcIntegralDatum l E)) (P.X n)) :
    (pbcDerivedExtend (rationalPullScalar l E sZ)).map
        ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app
          (DerivedCategory.Q.obj P)) ≫
      ac.ordinaryComparison.hom.app (DerivedCategory.Q.obj P) =
    ah.ordinaryComparison.hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj (DerivedCategory.Q.obj P)) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        (ag.ordinaryComparison.hom.app (DerivedCategory.Q.obj P)) ≫
      ambientComp.hom.app
        ((pbcDerivedExtend (rationalPullScalar l E sX)).obj (DerivedCategory.Q.obj P)) := by
  have : IsIso (pbcComplexCounit (rationalPullScalar l E sX) P) :=
    pbcComplexCounit_isIso _ P hP
  have := rationalPullComplexCounit_isIso l E (h ≫ g) ac.rationalCoefficient
    ac.rational_normalization
    (((pbcExtend (rationalPullScalar l E sX)).mapHomologicalComplex (.up ℤ)).obj P)
  rw [← cancel_mono ((rationalPullDerived l E (h ≫ g) ac.rationalCoefficient).map
      (pbcComplexCounit (rationalPullScalar l E sX) P) ≫
    rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient
      (((pbcExtend (rationalPullScalar l E sX)).mapHomologicalComplex (.up ℤ)).obj P))]
  have hΓ : (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app
        (DerivedCategory.Q.obj P) ≫
      pbcActualPullComplexCounit (h ≫ g) (pbcIntegralDatum l E) P =
    (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
        (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
      pbcActualPullComplexCounit h (pbcIntegralDatum l E)
        (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((pbcActualModulePullCompComplexIso h g (pbcIntegralDatum l E)).inv.app P) := by
    have hspec : (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).hom.app
          (DerivedCategory.Q.obj P) ≫
        (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcActualPullComplexCounit h (pbcIntegralDatum l E)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) =
      pbcActualPullComplexCounit (h ≫ g) (pbcIntegralDatum l E) P ≫
        DerivedCategory.Q.map
          ((pbcActualModulePullCompComplexIso h g (pbcIntegralDatum l E)).hom.app P) :=
      (pbcActualDerivedPullCompIso_exists h g (pbcIntegralDatum l E)).exists.choose_spec P hP hf'
    rw [← cancel_epi ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).hom.app
        (DerivedCategory.Q.obj P)),
      Iso.hom_inv_id_app_assoc, reassoc_of% hspec, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  -- The composite comparison, computed on complexes.
  rw [Category.assoc, ac.derived_normalization P, ← Functor.map_comp_assoc, hΓ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (pbcComplexCounit_naturality (rationalPullScalar l E sZ)
    ((pbcActualModulePullCompComplexIso h g (pbcIntegralDatum l E)).inv.app P))]
  -- The pasted comparison, computed on complexes.
  have hamb := ambientComp.hom.naturality (pbcComplexCounit (rationalPullScalar l E sX) P)
  simp only [Functor.comp_map] at hamb
  have hg : (rationalPullDerived l E h ah.rationalCoefficient).map
        (ag.ordinaryComparison.hom.app (DerivedCategory.Q.obj P)) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        ((rationalPullDerived l E g ag.rationalCoefficient).map
          (pbcComplexCounit (rationalPullScalar l E sX) P)) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        (rationalPullComplexCounit l E g ag.rationalCoefficient
          (((pbcExtend (rationalPullScalar l E sX)).mapHomologicalComplex (.up ℤ)).obj P)) =
    (rationalPullDerived l E h ah.rationalCoefficient).map
        ((pbcDerivedExtend (rationalPullScalar l E sY)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P)) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        (pbcComplexCounit (rationalPullScalar l E sY)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ag.moduleComparison (.up ℤ)).hom.app P)) := by
    simp only [← CategoryTheory.Functor.map_comp]
    rw [ag.derived_normalization P]
  rw [← reassoc_of% hamb, hderived, reassoc_of% hg]
  have hoc := ah.ordinaryComparison.hom.naturality
    (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P)
  simp only [Functor.comp_map] at hoc
  rw [← reassoc_of% hoc]
  erw [reassoc_of% (rationalPullComplexCounit_naturality l E h
    ah.rationalCoefficient ((NatIso.mapHomologicalComplex ag.moduleComparison (.up ℤ)).hom.app P))]
  erw [reassoc_of% (ah.derived_normalization
      (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P))]
  -- The two termwise maps agree by the module coherence.
  have hB := rationalModuleComparison_comp l E g h sX sY sZ ag ah ac moduleComp hmodule
  congr 3
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  ext n : 1
  simpa [pbcActualModulePullCompComplexIso] using hB (P.X n)

/-- The ordinary rational comparisons of composable pullbacks compose: on every integral object,
the comparison of the composite agrees with the pasting of the two comparisons, the derived
pullback compositor and the rational ambient compositor. -/
theorem rationalOrdinaryComparison_comp (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient ≅
        rationalPullModule l E (h ≫ g) ac.rationalCoefficient)
    (hmodule : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V)),
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (rationalCoherenceUnit l E h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (rationalCoherenceUnit l E g ag.rationalCoefficient M V m)) =
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (rationalCoherenceUnit l E (h ≫ g) ac.rationalCoefficient M V m))
    (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient ≅
        rationalPullDerived l E (h ≫ g) ac.rationalCoefficient)
    (hderived : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
      ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
          rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
        (rationalPullDerived l E h ah.rationalCoefficient).map
            (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
          rationalPullComplexCounit l E h ah.rationalCoefficient
            (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P))
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    (pbcDerivedExtend (rationalPullScalar l E sZ)).map
        ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj) ≫
      ac.ordinaryComparison.hom.app K.obj =
    ah.ordinaryComparison.hom.app ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        (ag.ordinaryComparison.hom.app K.obj) ≫
      ambientComp.hom.app ((pbcDerivedExtend (rationalPullScalar l E sX)).obj K.obj) := by
  let d := pbcIntegralDatum l E
  let α : (pbcActualDerivedPull g d ⋙ pbcActualDerivedPull h d) ⋙
      pbcDerivedExtend (rationalPullScalar l E sZ) ⟶
        pbcDerivedExtend (rationalPullScalar l E sX) ⋙
          rationalPullDerived l E (h ≫ g) ac.rationalCoefficient :=
    whiskerRight (pbcActualDerivedPullCompIso h g d).inv _ ≫ ac.ordinaryComparison.hom
  let β : (pbcActualDerivedPull g d ⋙ pbcActualDerivedPull h d) ⋙
      pbcDerivedExtend (rationalPullScalar l E sZ) ⟶
        pbcDerivedExtend (rationalPullScalar l E sX) ⋙
          rationalPullDerived l E (h ≫ g) ac.rationalCoefficient :=
    whiskerLeft (pbcActualDerivedPull g d) ah.ordinaryComparison.hom ≫
      whiskerRight ag.ordinaryComparison.hom (rationalPullDerived l E h ah.rationalCoefficient) ≫
      whiskerLeft (pbcDerivedExtend (rationalPullScalar l E sX)) ambientComp.hom
  change α.app K.obj = β.app K.obj
  obtain ⟨P, s, hP, hf, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (DerivedCategory.Q.objPreimage K.obj)
  have hf' (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion X d) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion X d) (P.X n)).symm (hf n)
  have : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  let i := asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K.obj
  rw [rationalOrdinary_app_eq_of_iso α i, rationalOrdinary_app_eq_of_iso β i]
  congr 2
  exact rationalOrdinaryComparison_comp_Q l E g h sX sY sZ ag ah ac moduleComp hmodule
    ambientComp hderived P hP hf'

/-- Inverting the completed-pullback units turns the ordinary composition coherence into the
composition coherence of the realization comparisons. -/
private theorem rationalCompletedComp_alpha_core (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient ≅
        rationalPullDerived l E (h ≫ g) ac.rationalCoefficient)
    {K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)}
    (hK : (pbcDerivedExtend (rationalPullScalar l E sZ)).map
        ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj) ≫
      ac.ordinaryComparison.hom.app K.obj =
    ah.ordinaryComparison.hom.app ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
      (rationalPullDerived l E h ah.rationalCoefficient).map
        (ag.ordinaryComparison.hom.app K.obj) ≫
      ambientComp.hom.app ((pbcDerivedExtend (rationalPullScalar l E sX)).obj K.obj))
    (φ : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h).obj
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) ⟶
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ g)).obj K.obj)
    (hφ : (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) ≫ φ =
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj) :
    haveI : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)) :=
      ah.integral.unit_isIso ((ag.integral.completedFunctor l E).obj K)
    haveI := ag.integral.unit_isIso K
    haveI := ac.integral.unit_isIso K
    (pbcDerivedExtend (rationalPullScalar l E sZ)).map φ ≫
        CategoryTheory.inv ((pbcDerivedExtend (rationalPullScalar l E sZ)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj)) ≫
        ac.ordinaryComparison.hom.app K.obj =
      CategoryTheory.inv ((pbcDerivedExtend (rationalPullScalar l E sZ)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
            ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj))) ≫
        ah.ordinaryComparison.hom.app
          ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) ≫
        (rationalPullDerived l E h ah.rationalCoefficient).map
          (CategoryTheory.inv ((pbcDerivedExtend (rationalPullScalar l E sY)).map
            ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj))) ≫
        (rationalPullDerived l E h ah.rationalCoefficient).map
          (ag.ordinaryComparison.hom.app K.obj) ≫
        ambientComp.hom.app ((pbcDerivedExtend (rationalPullScalar l E sX)).obj K.obj) := by
  have : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)) :=
    ah.integral.unit_isIso ((ag.integral.completedFunctor l E).obj K)
  have : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) :=
    ag.integral.unit_isIso K
  have : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj) :=
    ac.integral.unit_isIso K
  have hφ' : φ =
      CategoryTheory.inv ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)) ≫
      CategoryTheory.inv ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)) ≫
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj ≫
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj := by
    rw [← hφ]
    simp
  have hn := ah.ordinaryComparison.hom.naturality
    (CategoryTheory.inv ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj))
  simp only [Functor.comp_map, Functor.map_inv] at hn
  rw [hφ']
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  congr 1
  refine (congrArg (CategoryTheory.inv ((pbcDerivedExtend (rationalPullScalar l E sZ)).map
    ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj))) ≫ ·) hK).trans ?_
  exact (reassoc_of% hn) _

/-- Completed composition and descent to all raw rational fraction arrows. -/
theorem rationalCompletedPullbackComposition (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
    rationalPullModule l E h ah.rationalCoefficient ≅
  rationalPullModule l E (h ≫ g) ac.rationalCoefficient)
    (hmodule :
      let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (M : pbcModules T (rationalCoefficientSheaf l T E))
          (V : T.ProEt) (m : M.val.obj (op V)) :
          ((rationalPullModule l E g c).obj M).val.obj
            (op ((proEtaleBaseChange g).obj V)) :=
        pbcTensorSection c
          ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
      let scalarSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
          (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
        c.hom.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
            (rationalCoefficientSheaf l T E)).hom.app (op V) e)
      let scalarMul (T : Scheme.{u})
          (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
          (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
        e • m
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
        (m : M.val.obj (op V))
        (e' : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange g).obj V)))
        (e'' : (rationalCoefficientSheaf l Z E).obj.obj
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (scalarMul Z
          ((rationalPullModule l E h ah.rationalCoefficient).obj
            ((rationalPullModule l E g ag.rationalCoefficient).obj M))
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
          (unitSection h ah.rationalCoefficient
            ((rationalPullModule l E g ag.rationalCoefficient).obj M)
            ((proEtaleBaseChange g).obj V)
            (scalarMul Y
              ((rationalPullModule l E g ag.rationalCoefficient).obj M)
              (op ((proEtaleBaseChange g).obj V)) e'
              (unitSection g ag.rationalCoefficient M V m)))) =
        scalarMul Z
          ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
          (e'' * scalarSection h ah.rationalCoefficient
            ((proEtaleBaseChange g).obj V) e')
          (((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
            ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
              (unitSection (h ≫ g) ac.rationalCoefficient M V m))))
    (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
    rationalPullDerived l E h ah.rationalCoefficient ≅
  rationalPullDerived l E (h ≫ g) ac.rationalCoefficient)
    (hderived : (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
      rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
    (rationalPullDerived l E h ah.rationalCoefficient).map
        (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
      rationalPullComplexCounit l E h ah.rationalCoefficient
        (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P))) :
    ∃ (integralComp : ag.integral.completedFunctor l E ⋙ ah.integral.completedFunctor l E ≅
      ac.integral.completedFunctor l E),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
          ((ag.integral.completedFunctor l E).obj K).obj ≫
        (integralComp.hom.app K).hom =
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj) ∧
      ∃ (rawComp : ag.rawPull ⋙ ah.rawPull ≅ ac.rawPull),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      rawComp.hom.app
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        eqToHom (congrArg ah.rawPull.obj (ag.raw_objects K)) ≫
          eqToHom (ah.raw_objects ((ag.integral.completedFunctor l E).obj K)) ≫
          (pbcRationalization Z (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            (integralComp.hom.app K) ≫ eqToHom (ac.raw_objects K).symm) ∧
      (whiskerRight rawComp.hom sZ.J ≫ ac.alpha.hom =
      whiskerLeft ag.rawPull ah.alpha.hom ≫
        whiskerRight ag.alpha.hom (rationalPullDerived l E h ah.rationalCoefficient) ≫
        whiskerLeft sX.J ambientComp.hom) := by
  let d := pbcIntegralDatum l E
  let φ (K : PbcBoundedConstructibleComplete X d) :
      ((ag.integral.completedFunctor l E ⋙ ah.integral.completedFunctor l E).obj K).obj ≅
        ((ac.integral.completedFunctor l E).obj K).obj :=
    have := ah.integral.unit_isIso ((ag.integral.completedFunctor l E).obj K)
    have := ag.integral.unit_isIso K
    haveI := ac.integral.unit_isIso K
    (asIso ((pbcActualStrictCompletedPullUnit d h).app
        ((ag.integral.completedFunctor l E).obj K).obj)).symm ≪≫
      ((pbcActualDerivedPull h d).mapIso
        (asIso ((pbcActualStrictCompletedPullUnit d g).app K.obj))).symm ≪≫
      ((pbcActualDerivedPullCompIso h g d).app K.obj).symm ≪≫
      asIso ((pbcActualStrictCompletedPullUnit d (h ≫ g)).app K.obj)
  have hφ (K : PbcBoundedConstructibleComplete X d) :
      (pbcActualDerivedPull h d).map ((pbcActualStrictCompletedPullUnit d g).app K.obj) ≫
        (pbcActualStrictCompletedPullUnit d h).app
          ((ag.integral.completedFunctor l E).obj K).obj ≫ (φ K).hom =
      (pbcActualDerivedPullCompIso h g d).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit d (h ≫ g)).app K.obj := by
    simp [φ]
  have hnat {K L : PbcBoundedConstructibleComplete X d} (f : K ⟶ L) :
      ((ag.integral.completedFunctor l E ⋙ ah.integral.completedFunctor l E).map f).hom ≫
          (φ L).hom = (φ K).hom ≫ ((ac.integral.completedFunctor l E).map f).hom := by
    have : IsIso ((pbcActualStrictCompletedPullUnit d h).app
        ((pbcActualStrictCompletedPull d g).obj K.obj)) :=
      ah.integral.unit_isIso ((ag.integral.completedFunctor l E).obj K)
    have : IsIso ((pbcActualStrictCompletedPullUnit d g).app K.obj) :=
      ag.integral.unit_isIso K
    exact rationalCompletedComp_naturality (pbcActualStrictCompletedPullUnit d g)
      (pbcActualStrictCompletedPullUnit d h) (pbcActualStrictCompletedPullUnit d (h ≫ g))
      (pbcActualDerivedPullCompIso h g d).inv f.hom (hφ K) (hφ L)
  let integralComp : ag.integral.completedFunctor l E ⋙ ah.integral.completedFunctor l E ≅
      ac.integral.completedFunctor l E :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (φ K))
      (fun f ↦ ObjectProperty.hom_ext _ (hnat f))
  refine ⟨integralComp, hφ, ?_⟩
  let c (K : PbcRationalCategory X d (pbcUniformizer l E)) :
      ah.rawPull.obj (ag.rawPull.obj K) ≅ ac.rawPull.obj K :=
    eqToIso (congrArg ah.rawPull.obj (ag.raw_objects K.obj)) ≪≫
      eqToIso (ah.raw_objects ((ag.integral.completedFunctor l E).obj K.obj)) ≪≫
      (pbcRationalization Z d (pbcUniformizer l E)).mapIso (integralComp.app K.obj) ≪≫
        eqToIso (ac.raw_objects K.obj).symm
  have hc {K L : PbcRationalCategory X d (pbcUniformizer l E)} (f : K ⟶ L) :
      (ag.rawPull ⋙ ah.rawPull).map f ≫ (c L).hom = (c K).hom ≫ ac.rawPull.map f := by
    refine ScalarLocalization.naturality_of_localization (ag.rawPull ⋙ ah.rawPull) ac.rawPull
      (fun K ↦ (c K).hom) (fun K L f ↦ ?_) f
    change ah.rawPull.map (ag.rawPull.map ((pbcRationalization X d (pbcUniformizer l E)).map f)) ≫
      _ = _ ≫ ac.rawPull.map ((pbcRationalization X d (pbcUniformizer l E)).map f)
    rw [RationalRealizationPullbackComparison.rawPull_map_rationalization,
      RationalRealizationPullbackComparison.rawPull_map_rationalization,
      Functor.map_comp, Functor.map_comp,
      RationalRealizationPullbackComparison.rawPull_map_rationalization]
    simp only [c, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc]
    simp only [eqToHom_refl, Category.id_comp]
    have hn := congrArg (pbcRationalization Z d (pbcUniformizer l E)).map
      (integralComp.hom.naturality f)
    simp only [Functor.comp_map, Functor.map_comp] at hn
    erw [reassoc_of% hn]
    rfl
  refine ⟨NatIso.ofComponents c hc, fun K ↦ rfl, ?_⟩
  ext K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, NatIso.ofComponents_hom_app]
  have hA := rationalCompleted_app_eq_eqToHom ah.alpha.hom (ag.raw_objects K.obj)
  erw [hA]
  erw [RationalRealizationPullbackComparison.alpha_hom_app l E ac K.obj,
    RationalRealizationPullbackComparison.alpha_hom_app l E ag K.obj,
    RationalRealizationPullbackComparison.alpha_hom_app l E ah
      ((ag.integral.completedFunctor l E).obj K.obj)]
  simp only [c, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans_assoc]
  erw [RationalModuleRealization.map_rationalization]
  have hB := rationalCompleted_app_eq_eqToHom ambientComp.hom (sX.objects K.obj)
  erw [hB]
  simp only [Functor.comp_map, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  dsimp only [RationalPullIntegral.completedFunctor, pbcConditionalIntegral,
    ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [eqToHom_refl, Category.id_comp]
  have hunit (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V)) :
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (rationalCoherenceUnit l E h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (rationalCoherenceUnit l E g ag.rationalCoefficient M V m)) =
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (rationalCoherenceUnit l E (h ≫ g) ac.rationalCoefficient M V m) := by
    have hm := hmodule M V m 1 1
    simp only [one_smul, map_one, one_mul] at hm
    unfold rationalCoherenceUnit
    exact hm
  have hmid := rationalCompletedComp_alpha_core l E g h sX sY sZ ag ah ac ambientComp
    (rationalOrdinaryComparison_comp l E g h sX sY sZ ag ah ac moduleComp hunit
      ambientComp hderived K.obj) (integralComp.app K.obj).hom.hom (hφ K.obj)
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact hmid

end AlgebraicGeometry.Scheme
