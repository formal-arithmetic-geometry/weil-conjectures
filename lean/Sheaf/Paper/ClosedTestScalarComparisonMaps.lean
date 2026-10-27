module

public import Sheaf.Paper.ClosedTestKInjectiveSectionModels
public import Sheaf.Paper.ClosedTestDerivedExchangeModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Forward universal scalar comparisons

Source: Stacks Project, Tags 070Y, 09T5, 0D6D, 0D6F, 07A6 and 09BL
(blueprint: def-sfb-closed-test-scalar-comparison-maps).

The comparison maps use the universal right-derived units, without a flatness hypothesis.
UniversalCoherence and SectionCoherence spell out their normalization and compatibility
as equations, without asserting those equations as part of the definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]
/-- Exact scalar restriction on the recorded internal module category.
Source: Stacks 03EK (blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
abbrev restriction (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  Mod.comap (coefficientMap c X)

/-- The universal section comparison induced by the identity of underlying sections.
Source: Stacks 070Y (blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def gamma {X : Scheme.{u}} (W : X.ProEt) :
    (evaluation S W).rightDerivedFunctor ⟶
      restrict c X ⋙ (evaluation Λ W).rightDerivedFunctor :=
  Functor.rightDerivedPullback (restriction c X)
    (F := evaluation S W) (F' := evaluation Λ W) (𝟙 _)

/-- The literal section identity for direct image, right-derived on K-injectives.
Source: Stacks 0D6F (blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def derivedPushEvaluation (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) :
    CondensedRing.moduleObjectDerivedPushforward R b ⋙
        (evaluation R W).rightDerivedFunctor ≅
      (evaluation R (testFibre b W)).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar R b)
    (evaluation R W) (pushEvaluation R b W)

/-- The ordinary adjunction-unit section followed by restriction along a site arrow.
Source: Stacks 03D3, 09BL (blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def sectionArrow (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (b : X ⟶ Y)
    (W : Y.ProEt) (W' : X.ProEt) (t : W' ⟶ testFibre b W) :
    evaluation R W ⟶ CondensedRing.upperStar R b ⋙ evaluation R W' :=
  Functor.whiskerRight (CondensedRing.upperStarLowerStarAdjunction R b).unit
      (evaluation R W) ≫
    Functor.whiskerLeft (CondensedRing.upperStar R b)
      ((pushEvaluation R b W).hom ≫ evaluationMap R t)

/-- The derived section restriction specified by the actual ordinary unit section.
Source: Stacks 070Y, 03D3 (blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def derivedSectionArrow (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (b : X ⟶ Y)
    (W : Y.ProEt) (W' : X.ProEt) (t : W' ⟶ testFibre b W) :=
  Functor.rightDerivedPullback (CondensedRing.upperStar R b) (sectionArrow R b W W' t)

/-- Universal-unit, adjunction and ordinary-composition compatibility of the forward
scalar comparisons, including the actual unit--square--counit mate.
Source: Stacks 070Y, 09T5, 07A6, 0D6D
(blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def UniversalCoherence : Prop :=
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y)
      (P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)) ℤ),
    (restrict c Y).map ((CondensedRing.lowerStar S b).rightDerivedFunctorUnitQ P) ≫
        (restrictPush c b).app (DerivedCategory.Q.obj P) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ b).map
          ((restriction c X).mapDerivedCategoryFactors.hom.app P) =
      (restriction c Y).mapDerivedCategoryFactors.hom.app
          ((complexes (CondensedRing.lowerStar S b)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (CondensedRing.comapLowerStarIso c b).hom (.up ℤ)).app P) ≫
        (CondensedRing.lowerStar Λ b).rightDerivedFunctorUnitQ
          ((complexes (restriction c X)).obj P)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y)
      (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y))),
    (restrict c Y).map ((adj S b).unit.app M) ≫
        (restrictPush c b).app ((CondensedRing.upperStar S b).mapDerivedCategory.obj M) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ b).map
          ((CondensedRing.derivedComapUpperStarIso c b).hom.app M) =
      (adj Λ b).unit.app ((restrict c Y).obj M)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))),
    (restrict c X).map ((adj S b).counit.app N) =
      (CondensedRing.derivedComapUpperStarIso c b).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward S b).obj N) ≫
        (CondensedRing.upperStar Λ b).mapDerivedCategory.map ((restrictPush c b).app N) ≫
        (adj Λ b).counit.app ((restrict c X).obj N)) ∧
  (∀ {X Y Z : Scheme.{u}} (b : X ⟶ Y) (g : Y ⟶ Z)
      (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj S Z))),
    (CondensedRing.derivedComapUpperStarIso c b).hom.app
          ((CondensedRing.upperStar S g).mapDerivedCategory.obj M) ≫
        (CondensedRing.upperStar Λ b).mapDerivedCategory.map
          ((CondensedRing.derivedComapUpperStarIso c g).hom.app M) =
      (restrict c X).map ((pullComp S b g).inv.app M) ≫
        (CondensedRing.derivedComapUpperStarIso c (b ≫ g)).hom.app M ≫
        (pullComp Λ b g).hom.app ((restrict c Z).obj M)) ∧
  (∀ {X XZ U Z : Scheme.{u}} (f : X ⟶ U) (s : Z ⟶ U)
      (h : XZ ⟶ X) (fZ : XZ ⟶ Z) (w : h ≫ f = fZ ≫ s)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))),
    (CondensedRing.derivedComapUpperStarIso c s).inv.app
          ((CondensedRing.moduleObjectDerivedPushforward S f).obj N) ≫
        (restrict c Z).map ((ClosedTestDerivedExchangeModel.exchange S ⟨w⟩).app N) ≫
        (restrictPush c fZ).app ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((CondensedRing.derivedComapUpperStarIso c h).hom.app N) =
      (CondensedRing.upperStar Λ s).mapDerivedCategory.map ((restrictPush c f).app N) ≫
        (ClosedTestDerivedExchangeModel.exchange Λ ⟨w⟩).app ((restrict c X).obj N))

/-- Section-unit normalization and compatibility with actual unit sections, localization,
and the literal direct-image section formula. All scalar arrows point forward.
Source: Stacks 070Y, 0D6F, 09BL
(blueprint: def-sfb-closed-test-scalar-comparison-maps). -/
def SectionCoherence : Prop :=
  (∀ {X : Scheme.{u}} (W : X.ProEt)
      (P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)) ℤ),
    (evaluation S W).rightDerivedFunctorUnitQ P ≫
        (gamma c W).app (DerivedCategory.Q.obj P) ≫
        (evaluation Λ W).rightDerivedFunctor.map
          ((restriction c X).mapDerivedCategoryFactors.hom.app P) =
      (evaluation Λ W).rightDerivedFunctorUnitQ ((complexes (restriction c X)).obj P)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y)),
    (sectionArrow S b W W' t).app F ≫
        (evaluation Λ W').map ((CondensedRing.comapUpperStarIso c b).hom.app F) =
      (sectionArrow Λ b W W' t).app ((restriction c Y).obj F)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y))),
    (derivedSectionArrow S b W W' t).app N ≫
        (gamma c W').app ((CondensedRing.upperStar S b).mapDerivedCategory.obj N) ≫
        (evaluation Λ W').rightDerivedFunctor.map
          ((CondensedRing.derivedComapUpperStarIso c b).hom.app N) =
      (gamma c W).app N ≫
        (derivedSectionArrow Λ b W W' t).app ((restrict c Y).obj N)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))),
    (derivedPushEvaluation S b W).hom.app N ≫ (gamma c (testFibre b W)).app N =
      (gamma c W).app ((CondensedRing.moduleObjectDerivedPushforward S b).obj N) ≫
        (evaluation Λ W).rightDerivedFunctor.map ((restrictPush c b).app N) ≫
        (derivedPushEvaluation Λ b W).hom.app ((restrict c X).obj N))

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
