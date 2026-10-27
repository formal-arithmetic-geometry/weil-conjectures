/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.Paper.SectionDerivedTensorNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedSectionScalarTransport
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Normalization of the scalar-change direct-image unit

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D, 0D6E and 07A4;
Modules on Sites, Tags 03EK, 03EL and 0GMW
(blueprint: lem-sfb-scalar-change-direct-image-unit).

The scalar comparison data are the normalized witnesses of the recorded scalar
adjunction theorem. The pullback comparisons below are independently pinned by
ordinary balancing and universal computation counits. In particular the section
comparison is not defined by transporting the derived internal comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.all false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

/-- The witnesses and all normalizations of `InternalSectionScalarAdjunction`.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5
(blueprint: lem-sfb-scalar-change-direct-image-unit). -/
structure InternalSectionScalarData where
  sectionPair : SheafOfModules.ScalarDerivedPair (sectionScalarMap J a)
  restriction : Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
    (sectionModuleEquivalence J S).functor ⋙
      SheafOfModules.scalarRestriction (sectionScalarMap J a)
  extension : Mod.extendScalars a ⋙ (sectionModuleEquivalence J S).functor ≅
    (sectionModuleEquivalence J R).functor ⋙ sectionPair.extension
  internalDerived : DerivedCategory (scalarInternalModules J R) ⥤
    DerivedCategory (scalarInternalModules J S)
  internalCounit : DerivedCategory.Q ⋙ internalDerived ⟶
    (Mod.extendScalars a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  internalAdjunction : internalDerived ⊣ (Mod.comap a).mapDerivedCategory
  derivedRestriction : (Mod.comap a).mapDerivedCategory ⋙
      (sectionModuleEquivalence J R).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J S).functor.mapDerivedCategory ⋙
      SheafOfModules.scalarDerivedRestriction (sectionScalarMap J a)
  derivedExtension : internalDerived ⋙
      (sectionModuleEquivalence J S).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J R).functor.mapDerivedCategory ⋙ sectionPair.derived

namespace InternalSectionScalarData

/-- All section formulas, universal properties and localization normalizations.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5
(blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def Normalized (d : InternalSectionScalarData J a) : Prop :=
  (∀ (N : scalarInternalModules J S) (U : Cᵒᵖ)
  (x : N.X.obj.obj U), (d.restriction.hom.app N).val.app U x = x) ∧
  (∀ (M : scalarInternalModules J R) (U : Cᵒᵖ)
  (s : S.obj.obj U) (m : M.X.obj.obj U),
  ((eqToHom (d.sectionPair.extension_obj
    ((sectionModuleEquivalence J R).functor.obj M))).val.app U)
      ((d.extension.hom.app M).val.app U (internalScalarGenerator J a M U s m)) =
    (toSheafify J (SheafOfModules.changeOfRingsPresheaf (sectionScalarMap J a)
      ((sectionModuleEquivalence J R).functor.obj M)).presheaf).app U
        (s ⊗ₜ[(sectionRingSheaf J R).obj.obj U, ((sectionScalarMap J a).hom.app U).hom] m)) ∧
  (∀ (M : scalarInternalModules J R) (N : scalarInternalModules J S)
  (g : (Mod.extendScalars a).obj M ⟶ N),
  (sectionModuleEquivalence J R).functor.map
      ((Mod.extendRestrictAdjunction a).homEquiv M N g) ≫ d.restriction.hom.app N =
    d.sectionPair.ordinaryAdjunction.homEquiv _ _
      (d.extension.inv.app M ≫ (sectionModuleEquivalence J S).functor.map g)) ∧
  (d.internalDerived.IsLeftDerivedFunctor d.internalCounit
  (HomologicalComplex.quasiIso (scalarInternalModules J R) (.up ℤ))) ∧
  (∀ P : CochainComplex (scalarInternalModules J R) ℤ,
  CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
    (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
      IsIso (d.internalCounit.app P)) ∧
  (∀ P : CochainComplex (scalarInternalModules J R) ℤ,
  d.internalAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
      (Mod.comap a).mapDerivedCategory.map (d.internalCounit.app P) ≫
      (Mod.comap a).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((Mod.extendRestrictAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
  (d.derivedRestriction =
  (Functor.mapDerivedCategoryCompIso (Mod.comap a)
    (sectionModuleEquivalence J R).functor).symm ≪≫
  Functor.mapDerivedCategoryNatIso d.restriction ≪≫
  Functor.mapDerivedCategoryCompIso (sectionModuleEquivalence J S).functor
    (SheafOfModules.scalarRestriction (sectionScalarMap J a))) ∧
  (∀ P : CochainComplex (scalarInternalModules J R) ℤ,
  CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
    (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := sectionRingSheaf J R)
    ((sectionModuleEquivalence J R).functor.obj (P.X n))) →
  (sectionModuleEquivalence J S).functor.mapDerivedCategory.map (d.internalCounit.app P) ≫
      (sectionModuleEquivalence J S).functor.mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d.extension (.up ℤ)).hom.app P) =
    d.derivedExtension.hom.app (DerivedCategory.Q.obj P) ≫
      d.sectionPair.derived.map
        ((sectionModuleEquivalence J R).functor.mapDerivedCategoryFactors.hom.app P) ≫
      SheafOfModules.scalarPairComplexComparison d.sectionPair.extension
        d.sectionPair.extension_additive d.sectionPair.derived d.sectionPair.counit
        (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  (∀ (M : DerivedCategory (scalarInternalModules J R))
  (N : DerivedCategory (scalarInternalModules J S)) (g : d.internalDerived.obj M ⟶ N),
  (sectionModuleEquivalence J R).functor.mapDerivedCategory.map
      (d.internalAdjunction.homEquiv M N g) ≫ d.derivedRestriction.hom.app N =
    d.sectionPair.adjunction.homEquiv _ _
      (d.derivedExtension.inv.app M ≫
        (sectionModuleEquivalence J S).functor.mapDerivedCategory.map g))

end InternalSectionScalarData

end CategoryTheory.InternalAbelianSheafModule

end

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits
open InternalAbelianSheafModule
open scoped CategoryTheory.Obj
attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence

namespace AlgebraicGeometry.ProEtale.ScalarDirectImageUnit
open ModuleRingedComparison

/-- Paste two comparison squares using only functor associators and whiskering.
Source: Stacks 07A6, composition of specified comparisons
(blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def comparisonComp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C] {A' : Type u₄} [Category.{v₄} A']
    {B' : Type u₅} [Category.{v₅} B'] {C' : Type u₆} [Category.{v₆} C']
    {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'}
    (p : F ⋙ EB ≅ EA ⋙ F') (q : G ⋙ EC ≅ EB ⋙ G') :
    (F ⋙ G) ⋙ EC ≅ EA ⋙ (F' ⋙ G') :=
  Functor.associator F G EC ≪≫ Functor.isoWhiskerLeft F q ≪≫
    (Functor.associator F EB G').symm ≪≫ Functor.isoWhiskerRight p G' ≪≫
    Functor.associator EA F' G'

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules S T)]

/-- The existing normalized comparison witnesses on a specified pro-etale site.
Source: Stacks 03EK and 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
abbrev ScalarData (T : Scheme.{u}) :=
  InternalSectionScalarData.{u + 1, u + 1, u, u + 1} (Scheme.ProEt.topology T) (coefficientMap a T)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (dX : ScalarData a X) (dY : ScalarData a Y)

/-- Ordinary section-ring balancing is specified on the fixed equivalence images.
Its value is independent of any derived comparison. Essential surjectivity makes
this component normalization determine at most one natural isomorphism.
Source: Stacks 03EL and 07A4 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def OrdinarySectionPullNormalized
    (b : dY.sectionPair.extension ⋙ ModuleRingedComparison.pullback S f ≅
      ModuleRingedComparison.pullback R f ⋙ dX.sectionPair.extension) : Prop :=
  Functor.isoWhiskerLeft (equivalence R Y).functor b =
    (comparisonComp
      (F := Mod.extendScalars (coefficientMap a Y)) (G := CondensedRing.upperStar S f)
      (F' := dY.sectionPair.extension) (G' := ModuleRingedComparison.pullback S f)
      (EA := (equivalence R Y).functor) (EB := (equivalence S Y).functor)
      (EC := (equivalence S X).functor) dY.extension (pullComparison S f)).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.pullIso a f).symm (equivalence S X).functor ≪≫
      comparisonComp
        (F := CondensedRing.upperStar R f) (G := Mod.extendScalars (coefficientMap a X))
        (F' := ModuleRingedComparison.pullback R f) (G' := dX.sectionPair.extension)
        (EA := (equivalence R Y).functor) (EB := (equivalence R X).functor)
        (EC := (equivalence S X).functor) (pullComparison R f) dX.extension

/-- Ordinary restriction/pullback is fixed by identified inverse image and the
identity-on-sections scalar square, on every object in the equivalence image.
Source: Stacks 03EL and 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def OrdinarySectionRestrictionNormalized
    (r : ModuleRingedComparison.pullback S f ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ≅
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ⋙
        ModuleRingedComparison.pullback R f) :
    Prop :=
  Functor.isoWhiskerLeft (equivalence S Y).functor r =
    (comparisonComp
      (F := CondensedRing.upperStar S f)
      (G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap a X))
      (F' := ModuleRingedComparison.pullback S f)
      (G' := SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)))
      (EA := (equivalence S Y).functor) (EB := (equivalence S X).functor)
      (EC := (equivalence R X).functor) (pullComparison S f) dX.restriction).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.comapUpperStarIso a f) (equivalence R X).functor ≪≫
      comparisonComp
        (F := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (coefficientMap a Y)) (G := CondensedRing.upperStar R f)
        (F' := SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)))
        (G' := ModuleRingedComparison.pullback R f)
        (EA := (equivalence S Y).functor) (EB := (equivalence R Y).functor)
        (EC := (equivalence R X).functor) dY.restriction (pullComparison R f)

variable (r : ModuleRingedComparison.pullback S f ⋙
    SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ≅
  SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ⋙
        ModuleRingedComparison.pullback R f)

/-- Localization of the identified-coefficient inverse-image restriction comparison.
Source: Stacks 0D6D and 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def sectionRestrictionPull :
    derivedPullback S f ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ≅
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ⋙
          derivedPullback R f :=
  (Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.pullback S f)
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
    Functor.mapDerivedCategoryCompIso
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)))
      (ModuleRingedComparison.pullback R f)

/-- The adjunction-compatible section-ring direct-image comparison. Its precise
mate equation is the characterization in the recorded ring-sheaf change theorem.
Source: Stacks 0D6E and 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def sectionRestrictionPush :
    derivedPushforward S f ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ⟶
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
          derivedPushforward R f :=
  (mateEquiv (derivedAdjunction S f) (derivedAdjunction R f)
    (TwoSquare.mk _ _ _ _ (sectionRestrictionPull a f r).inv)).natTrans

/-- The actual geometric computation map on a complex, using exact module pullback.
Source: Stacks 0D6D (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def internalPullCompute
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (P : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
      (DerivedCategory.Q.obj P) ≫
    (CondensedRing.upperStar Λ f).mapDerivedCategoryFactors.hom.app P

/-- Scalar/pullback comparison pinned by its universal computation-counit square.
On flat-term K-flat representatives the ordinary bottom map is the fixed
pure-tensor balancing map with the pulled-back coefficient identifications.
Source: Stacks 0D6D and 07A4 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def InternalPullNormalized
    (b : dY.internalDerived ⋙ internalDerivedPullback S f ≅
      internalDerivedPullback R f ⋙ dX.internalDerived) : Prop :=
  ∀ P : CochainComplex (internalModules R Y) ℤ,
    b.hom.app (DerivedCategory.Q.obj P) ≫
        dX.internalDerived.map (internalPullCompute f R P) ≫
        dX.internalCounit.app
          (((CondensedRing.upperStar R f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (CondensedRing.upperStar R f ⋙
            Mod.extendScalars (coefficientMap a X))) (.up ℤ)).hom.app P) =
      (internalDerivedPullback S f).map (dY.internalCounit.app P) ≫
        internalPullCompute f S
          (((Mod.extendScalars (coefficientMap a Y)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (CondensedRing.pullIso a f).symm (.up ℤ)).hom.app P)

/-- The independent section-ring normalization, using its actual scalar universal
counit, exact geometric localization, and ordinary section-ring balancing map.
Source: Stacks 0D6D and 07A4 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def SectionPullNormalized
    (b₀ : dY.sectionPair.extension ⋙ ModuleRingedComparison.pullback S f ≅
      ModuleRingedComparison.pullback R f ⋙ dX.sectionPair.extension)
    (b : dY.sectionPair.derived ⋙ derivedPullback S f ≅
      derivedPullback R f ⋙ dX.sectionPair.derived) : Prop :=
  ∀ P : CochainComplex (modules R Y) ℤ,
    b.hom.app (DerivedCategory.Q.obj P) ≫
        dX.sectionPair.derived.map
          ((ModuleRingedComparison.pullback R f).mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison dX.sectionPair.extension
          dX.sectionPair.extension_additive dX.sectionPair.derived dX.sectionPair.counit
          (((ModuleRingedComparison.pullback R f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleRingedComparison.pullback R f ⋙ dX.sectionPair.extension))
          (.up ℤ)).hom.app P) =
      (derivedPullback S f).map
          (SheafOfModules.scalarPairComplexComparison dY.sectionPair.extension
            dY.sectionPair.extension_additive dY.sectionPair.derived dY.sectionPair.counit P) ≫
        (ModuleRingedComparison.pullback S f).mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.scalarComplex dY.sectionPair.extension
            dY.sectionPair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          b₀ (.up ℤ)).hom.app P)

/-- The internal direct-image comparison is exactly the S-geometric adjunct of
balancing followed by scalar extension of the R-geometric counit.
Source: Stacks 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def internalBeta
    (b : dY.internalDerived ⋙ internalDerivedPullback S f ≅
      internalDerivedPullback R f ⋙ dX.internalDerived)
    (C : DerivedCategory (internalModules R X)) :
    dY.internalDerived.obj ((internalDerivedPushforward R f).obj C) ⟶
      (internalDerivedPushforward S f).obj (dX.internalDerived.obj C) :=
  (normalizationInternalAdjunction S f).homEquiv _ _
    (b.hom.app ((internalDerivedPushforward R f).obj C) ≫
      dX.internalDerived.map ((normalizationInternalAdjunction R f).counit.app C))

/-- The section-ring comparison, independently defined by the same counit formula.
Source: Stacks 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def sectionBeta
    (b : dY.sectionPair.derived ⋙ derivedPullback S f ≅
      derivedPullback R f ⋙ dX.sectionPair.derived)
    (C : DerivedCategory (modules R X)) :
    dY.sectionPair.derived.obj ((derivedPushforward R f).obj C) ⟶
      (derivedPushforward S f).obj (dX.sectionPair.derived.obj C) :=
  (derivedAdjunction S f).homEquiv _ _
    (b.hom.app ((derivedPushforward R f).obj C) ≫
      dX.sectionPair.derived.map ((derivedAdjunction R f).counit.app C))

/-- The restricted section comparison followed by the canonical direct-image comparison.
Source: Stacks 0D6E and 07A6 (blueprint: lem-sfb-scalar-change-direct-image-unit). -/
def sectionT
    (b : dY.sectionPair.derived ⋙ derivedPullback S f ≅
      derivedPullback R f ⋙ dX.sectionPair.derived)
    (C : DerivedCategory (modules R X)) :
    (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (coefficientMap a Y))).obj
          (dY.sectionPair.derived.obj ((derivedPushforward R f).obj C)) ⟶
      (derivedPushforward R f).obj
        ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (coefficientMap a X))).obj
              (dX.sectionPair.derived.obj C)) :=
  (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y))).map
        (sectionBeta (R := R) (S := S) (a := a) f dX dY b C) ≫
    (sectionRestrictionPush a f r).app (dX.sectionPair.derived.obj C)

/-- The scalar-change direct-image mate is preserved by reconstruction, satisfies
its scalar-unit equation, and intertwines inverse integer multiplication.
Source: Stacks 07A6, 0D6D, 0D6E and 07A4
(blueprint: lem-sfb-scalar-change-direct-image-unit).

Proof:
1. Ordinary balancing uses c_R and c_S, compatible with a by naturality of the
coefficient comparison from the point. It sends f⁻¹(s tensor m) to
c_S(f⁻¹s) tensor f⁻¹m. Internal/section scalar, tensor and geometric normalizations
identify this actual arrow and both independently specified geometric counits.
2. Universal computation-counit squares on flat-term K-flat resolutions uniquely
determine the two pullback comparisons. Reconstruction identifies their squares.
Taking the S-geometric adjunct therefore identifies the two beta maps.
3. The ring-sheaf change-adjunction theorem identifies the section restriction
comparison d with the mate of the identified-coefficient inverse-image square.
Thus the R-geometric adjunct of t is U_X(q) after the inverse restriction/pullback
comparison, where q=L_X(epsilon_C) after theta.
4. Exact scalar extension and exact geometric pullback allow termwise computation.
On flat-term K-flat representatives their unit square sends f⁻¹m to
f⁻¹(1 tensor m), then to 1 tensor f⁻¹m. These are inverse-image sheaf morphisms
before balancing and sheafification, so this is not a geometric-point test.
5. Naturality of the scalar unit makes the adjunct of eta_M followed by t equal
to epsilon_C followed by eta_C. Naturality of the geometric counit gives that
same adjunct for Rf_*(eta_C). Injectivity of the adjunction bijection gives equality.
6. All comparison equivalences and module operations preserve integer scalars.
If s is invertible in S, its pullbacks give inverse multiplication on both
scalar extensions. Integer multiplication commutes with every derived morphism;
invert that square to obtain the last displayed equation. This argument includes
zero coefficients, zero complexes, identity maps and arbitrary unbounded complexes.
-/
theorem scalar_change_direct_image_unit
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Y))]
    (hX : dX.Normalized (Scheme.ProEt.topology X) (coefficientMap a X))
    (hY : dY.Normalized (Scheme.ProEt.topology Y) (coefficientMap a Y)) :
    (∃! b₀ : dY.sectionPair.extension ⋙ ModuleRingedComparison.pullback S f ≅
      ModuleRingedComparison.pullback R f ⋙ dX.sectionPair.extension,
        OrdinarySectionPullNormalized a f dX dY b₀) ∧
    (∃! r₀ : ModuleRingedComparison.pullback S f ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ≅
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ⋙
        ModuleRingedComparison.pullback R f,
        OrdinarySectionRestrictionNormalized a f dX dY r₀) ∧
    ∀ (b₀ : dY.sectionPair.extension ⋙ ModuleRingedComparison.pullback S f ≅
      ModuleRingedComparison.pullback R f ⋙ dX.sectionPair.extension),
      OrdinarySectionPullNormalized a f dX dY b₀ →
      OrdinarySectionRestrictionNormalized a f dX dY r →
    (∃ b : dY.internalDerived ⋙ internalDerivedPullback S f ≅
      internalDerivedPullback R f ⋙ dX.internalDerived,
        InternalPullNormalized a f dX dY b) ∧
    (∃ b : dY.sectionPair.derived ⋙ derivedPullback S f ≅
      derivedPullback R f ⋙ dX.sectionPair.derived,
        SectionPullNormalized a f dX dY b₀ b) ∧
    IsIso (sectionRestrictionPush a f r) ∧
    ∀ (bI : dY.internalDerived ⋙ internalDerivedPullback S f ≅
        internalDerivedPullback R f ⋙ dX.internalDerived)
      (bS : dY.sectionPair.derived ⋙ derivedPullback S f ≅
        derivedPullback R f ⋙ dX.sectionPair.derived),
      InternalPullNormalized a f dX dY bI → SectionPullNormalized a f dX dY b₀ bS →
      ∀ C : DerivedCategory (internalModules R X),
    ((derivedEquivalence S Y).functor.map (internalBeta (R := R) (S := S) (a := a) f dX dY bI C) ≫
        (derivedPushComparison S f).hom.app (dX.internalDerived.obj C) ≫
        (derivedPushforward S f).map (dX.derivedExtension.hom.app C) =
      dY.derivedExtension.hom.app ((internalDerivedPushforward R f).obj C) ≫
        dY.sectionPair.derived.map ((derivedPushComparison R f).hom.app C) ≫
        sectionBeta (R := R) (S := S) (a := a) f dX dY bS
          ((derivedEquivalence R X).functor.obj C)) ∧
    (dY.sectionPair.adjunction.unit.app
        ((derivedPushforward R f).obj ((derivedEquivalence R X).functor.obj C)) ≫
        sectionT a f dX dY r bS ((derivedEquivalence R X).functor.obj C) =
      (derivedPushforward R f).map
        (dX.sectionPair.adjunction.unit.app ((derivedEquivalence R X).functor.obj C))) ∧
    (∀ s : ℤ, IsIso (s • 𝟙 S) →
      ∃ v : Aut ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y))).obj
            (dY.sectionPair.derived.obj
              ((derivedPushforward R f).obj ((derivedEquivalence R X).functor.obj C)))),
      ∃ w : Aut ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X))).obj
            (dX.sectionPair.derived.obj ((derivedEquivalence R X).functor.obj C))),
      v.inv = s • 𝟙 _ ∧ w.inv = s • 𝟙 _ ∧
        v.hom ≫ sectionT a f dX dY r bS ((derivedEquivalence R X).functor.obj C) =
          sectionT a f dX dY r bS ((derivedEquivalence R X).functor.obj C) ≫
            (derivedPushforward R f).map w.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.ScalarDirectImageUnit
