/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.Paper.SectionDerivedTensorNormalization
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-! # Internal-to-section normalization of the scalar projection mate

Source: blueprint main-20261015, lem-sfb-dc-lower-star-preserves.proof.md, last paragraph;
Stacks Project, Tags 03EL, 07A4, 09T5 and 0B56, equation-projection-formula-map
(blueprint: lem-sfb-internal-scalar-projection-mate).

The equality is written after applying the fixed section equivalence. Its tensor and
geometric comparisons are the normalized comparisons imported above. The scalar-tensor
identifications are existential witnesses pinned by ordinary generators and their
localization square; no arbitrary isomorphism is selected as data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']


/-- The actual restricted regular coefficient module, not a replacement coefficient.
Source: Stacks 03EK (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :=
  (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T)).obj
    (𝟙_ (internalModules Λ' T))


/-- The coefficient in degree zero, using the existing single-complex functor.
Source: Stacks 06YY (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionCoefficientComplex (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :=
  (CochainComplex.singleFunctor (internalModules Λ T) (0 : ℤ)).obj
    (scalarProjectionCoefficient a T)


/-- The localized coefficient module in the ordinary unbounded derived category.
Source: Stacks 06YY (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionDerivedCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :=
  DerivedCategory.Q.obj (scalarProjectionCoefficientComplex a T)


/-- Cartesian identification of the pulled-back restricted regular coefficient.
Source: Stacks 03EL (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionCoefficientPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj (scalarProjectionCoefficient a Y) ⟶
      scalarProjectionCoefficient a X :=
  (CondensedRing.comapUpperStarIso a f).inv.app (𝟙_ (internalModules Λ' Y)) ≫
    (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a X)).map
      ((internalPullOplax Λ' f).η)


/-- Localize the actual coefficient identification, with the exact pullback factors.
Source: Stacks 07A4 (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionDerivedCoefficientPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback Λ f).obj (scalarProjectionDerivedCoefficient a Y) ⟶
      scalarProjectionDerivedCoefficient a X :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
      (scalarProjectionDerivedCoefficient a Y) ≫
    (CondensedRing.upperStar Λ f).mapDerivedCategoryFactors.hom.app
      (scalarProjectionCoefficientComplex a Y) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (CondensedRing.upperStar Λ f) (.up ℤ) 0).hom.app
          (scalarProjectionCoefficient a Y)) ≫
    DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (internalModules Λ X) (0 : ℤ)).map
        (scalarProjectionCoefficientPull a f))


variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The recorded internal derived adjunction with its endpoints fixed.
Source: Stacks 09T5 (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionInternalAdjunction
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPullback R f ⊣ internalDerivedPushforward R f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction R f

/-- The specified symmetric projection arrow: transpose tensor comparison then counit.
Source: Stacks 0B56 (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionCounitMate (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : DerivedCategory (internalModules Λ X)) :
    ((CondensedRing.derivedTensor Λ Y).obj
      (scalarProjectionDerivedCoefficient a Y)).obj ((internalDerivedPushforward Λ f).obj C) ⟶
      (internalDerivedPushforward Λ f).obj
        (((CondensedRing.derivedTensor Λ X).obj (scalarProjectionDerivedCoefficient a X)).obj C) :=
  (scalarProjectionInternalAdjunction Λ f).homEquiv
    (((CondensedRing.derivedTensor Λ Y).obj
      (scalarProjectionDerivedCoefficient a Y)).obj ((internalDerivedPushforward Λ f).obj C))
    (((CondensedRing.derivedTensor Λ X).obj (scalarProjectionDerivedCoefficient a X)).obj C)
    (((internalDelta Λ f).app (scalarProjectionDerivedCoefficient a Y)).app
        ((internalDerivedPushforward Λ f).obj C) ≫
      ((CondensedRing.derivedTensor Λ X).map
        (scalarProjectionDerivedCoefficientPull a f)).app
          ((internalDerivedPullback Λ f).obj ((internalDerivedPushforward Λ f).obj C)) ≫
      ((CondensedRing.derivedTensor Λ X).obj (scalarProjectionDerivedCoefficient a X)).map
        ((scalarProjectionInternalAdjunction Λ f).counit.app C))


variable (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
    (AlgebraicGeometry.ProEtale.coefficientMap a T))]

/-- Canonical scalar restriction on unbounded derived internal modules.
Source: Stacks 03EK (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionRestriction (T : Scheme.{u}) :
    DerivedCategory (internalModules Λ' T) ⥤ DerivedCategory (internalModules Λ T) :=
  (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T)).mapDerivedCategory

/-- The specified total derived scalar extension.
Source: Stacks 06YY (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionExtension (T : Scheme.{u}) :
    DerivedCategory (internalModules Λ T) ⥤ DerivedCategory (internalModules Λ' T) :=
  (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T)).leftDerivedFunctor

/-- Restriction commutes with geometric pullback via the actual Cartesian square.
Source: Stacks 03EL (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionRestrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPullback Λ' f ⋙ scalarProjectionRestriction a X ≅
      scalarProjectionRestriction a Y ⋙ internalDerivedPullback Λ f :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f)
      (scalarProjectionRestriction a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a f ≪≫
    Functor.isoWhiskerLeft (scalarProjectionRestriction a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

/-- The scalar pullback arrow is the actual tensor pullback arrow after restriction.
Source: Stacks 03EL and 07A4
(blueprint: lem-sfb-internal-scalar-projection-mate). -/
def ScalarProjectionPullTransport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ T : Scheme.{u},
      scalarProjectionExtension a T ⋙ scalarProjectionRestriction a T ≅
        (CondensedRing.derivedTensor Λ T).obj (scalarProjectionDerivedCoefficient a T)) :
    Prop :=
  ∀ A : DerivedCategory (internalModules Λ Y),
    (internalDerivedPullback Λ f).map ((h Y).inv.app A) ≫
        (scalarProjectionRestrictionPull a f).inv.app ((scalarProjectionExtension a Y).obj A) ≫
        (scalarProjectionRestriction a X).map ((CondensedRing.derivedPullIso a f).inv.app A) ≫
        (h X).hom.app ((internalDerivedPullback Λ f).obj A) =
      ((internalDelta Λ f).app (scalarProjectionDerivedCoefficient a Y)).app A ≫
        ((CondensedRing.derivedTensor Λ X).map
          (scalarProjectionDerivedCoefficientPull a f)).app
            ((internalDerivedPullback Λ f).obj A)

/-- The derived scalar/tensor comparison is localization of its ordinary generator map.
Source: Stacks 06YY and 07A4
(blueprint: lem-sfb-internal-scalar-projection-mate). -/
def ScalarProjectionDerivedTensorNormalization
    (e : ∀ T : Scheme.{u},
      Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T) ⋙
          Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T) ≅
        tensorLeft (scalarProjectionCoefficient a T))
    (h : ∀ T : Scheme.{u},
      scalarProjectionExtension a T ⋙ scalarProjectionRestriction a T ≅
        (CondensedRing.derivedTensor Λ T).obj (scalarProjectionDerivedCoefficient a T)) :
    Prop :=
  ∀ (T : Scheme.{u}) (P : CochainComplex (internalModules Λ T) ℤ),
  (h T).hom.app (DerivedCategory.Q.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (scalarProjectionCoefficientComplex a T) P ≫
      DerivedCategory.Q.map
        (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (internalModules Λ T))
          (scalarProjectionCoefficient a T) P).hom =
    (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T)).mapDerivedCategory.map
      ((Functor.leftDerivedFunctorIsoMapDerivedCategory
        (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T))).hom.app
          (DerivedCategory.Q.obj P)) ≫
    (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T)).mapDerivedCategory.map
      ((Functor.mapDerivedCategoryFactors
        (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T))).hom.app P) ≫
    (Functor.mapDerivedCategoryFactors
      (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T))).hom.app
        (((Mod.extendScalars
          (AlgebraicGeometry.ProEtale.coefficientMap a T)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (e T) (.up ℤ)).hom.app P)

/-- The actual section-ring coefficient map.
Source: Stacks 03EK (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionSectionMap (T : Scheme.{u}) : ring Λ T ⟶ ring Λ' T :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (AlgebraicGeometry.ProEtale.coefficientMap a T)

/-- Ordinary section-ring restriction with the site and coefficient universes explicit.
Source: Stacks 03EK (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionSectionRestriction (T : Scheme.{u}) : modules Λ' T ⥤ modules Λ T :=
  SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology T) (scalarProjectionSectionMap a T)

/-- The recorded section restriction localized on the ordinary unbounded categories.
Source: Stacks 07A6 (blueprint: lem-sfb-internal-scalar-projection-mate). -/
abbrev scalarProjectionSectionDerivedRestriction (T : Scheme.{u}) :
    DerivedCategory (modules Λ' T) ⥤ DerivedCategory (modules Λ T) :=
  SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
    (J := Scheme.ProEt.topology T) (scalarProjectionSectionMap a T)

/-- The actual exact-functor comparison on a complex for the specified scalar extension.
Source: Stacks 06YY (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionExtensionFactor (T : Scheme.{u})
    (P : CochainComplex (internalModules Λ T) ℤ) :
    (scalarProjectionExtension a T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((Mod.extendScalars
        (AlgebraicGeometry.ProEtale.coefficientMap a T)).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.leftDerivedFunctorIsoMapDerivedCategory
    (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T))).hom.app
      (DerivedCategory.Q.obj P) ≫
    (Functor.mapDerivedCategoryFactors
      (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T))).hom.app P

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Named scalar identifications on this site, tied to the specified internal extension.
The section extension is the sheafified balanced tensor and its universal derived pair.
The last square pins the SAME derivedExtension on flat-term K-flat representatives.
Source: Stacks 03EK, 06YY and 07A6
(blueprint: lem-sfb-internal-scalar-projection-mate). -/
structure ScalarProjectionSectionIdentifications (T : Scheme.{u}) where
  /-- The independently normalized section-ring scalar pair. -/
  sectionPair : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
    (J := Scheme.ProEt.topology T) (scalarProjectionSectionMap a T)
  /-- Restriction comparison on ordinary modules. -/
  restriction : Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T) ⋙
      (equivalence Λ T).functor ≅
    (equivalence Λ' T).functor ⋙
      scalarProjectionSectionRestriction a T
  /-- Restriction leaves every underlying section unchanged. -/
  restriction_sections : ∀ (N : internalModules Λ' T) (W : T.ProEtᵒᵖ)
    (x : N.X.obj.obj W), (restriction.hom.app N).val.app W x = x
  /-- Ordinary extension comparison. -/
  extension : Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T) ⋙
      (equivalence Λ' T).functor ≅ (equivalence Λ T).functor ⋙ sectionPair.extension
  /-- Its ordinary unit normalization determines the balanced generator map. -/
  extension_unit : ∀ (M : internalModules Λ T),
    (equivalence Λ T).functor.map
        ((Mod.extendRestrictAdjunction
          (AlgebraicGeometry.ProEtale.coefficientMap a T)).unit.app M) ≫
      restriction.hom.app
        ((Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T)).obj M) =
    sectionPair.ordinaryAdjunction.unit.app ((equivalence Λ T).functor.obj M) ≫
      (scalarProjectionSectionRestriction a T).map
        (extension.inv.app M)
  /-- Derived restriction between the actual named functors. -/
  derivedRestriction : scalarProjectionRestriction a T ⋙ derivedFunctor Λ T ≅
    derivedFunctor Λ' T ⋙ scalarProjectionSectionDerivedRestriction a T
  /-- This comparison is the localization of restriction, rather than a fresh choice. -/
  derivedRestriction_eq : derivedRestriction = Functor.mapDerivedCategorySquareIso restriction
  /-- Derived extension between the actual named internal and section functors. -/
  derivedExtension : scalarProjectionExtension a T ⋙ derivedFunctor Λ' T ≅
    derivedFunctor Λ T ⋙ sectionPair.derived
  /-- K-flat normalization uses the actual extension factor and the same ordinary extension. -/
  derivedExtension_kflat : ∀ (P : CochainComplex (internalModules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T) (R := ring Λ T)
      ((equivalence Λ T).functor.obj (P.X n))) →
    (derivedFunctor Λ' T).map (scalarProjectionExtensionFactor a T P) ≫
        (equivalence Λ' T).functor.mapDerivedCategoryFactors.hom.app
          ((Functor.mapHomologicalComplex
            (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T)) (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) =
      derivedExtension.hom.app (DerivedCategory.Q.obj P) ≫
        sectionPair.derived.map ((equivalence Λ T).functor.mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          (J := Scheme.ProEt.topology T) sectionPair.extension
          sectionPair.extension_additive sectionPair.derived sectionPair.counit
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- Section restriction/pullback comparison, explicitly using the named scalar comparisons.
Source: Stacks 03EL (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionSectionRestrictionPull
    (d : ∀ T : Scheme.{u}, ScalarProjectionSectionIdentifications a T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : DerivedCategory (internalModules Λ' Y)) :
    (derivedPullback Λ f).obj
        ((scalarProjectionSectionDerivedRestriction a Y).obj
          ((derivedFunctor Λ' Y).obj N)) ⟶
      (scalarProjectionSectionDerivedRestriction a X).obj
        ((derivedPullback Λ' f).obj ((derivedFunctor Λ' Y).obj N)) :=
  (derivedPullback Λ f).map ((d Y).derivedRestriction.inv.app N) ≫
    (derivedPullComparison Λ f).inv.app ((scalarProjectionRestriction a Y).obj N) ≫
    (derivedFunctor Λ X).map ((scalarProjectionRestrictionPull a f).inv.app N) ≫
    (d X).derivedRestriction.hom.app ((internalDerivedPullback Λ' f).obj N) ≫
    (scalarProjectionSectionDerivedRestriction a X).map
      ((derivedPullComparison Λ' f).hom.app N)

/-- The actual inverse derivedPullIso in section-ring coordinates.
Source: Stacks 03EL and 07A4 (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionSectionPull
    (d : ∀ T : Scheme.{u}, ScalarProjectionSectionIdentifications a T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : DerivedCategory (internalModules Λ Y)) :
    (derivedPullback Λ' f).obj
        ((derivedFunctor Λ' Y).obj ((scalarProjectionExtension a Y).obj A)) ⟶
      (d X).sectionPair.derived.obj
        ((derivedPullback Λ f).obj ((derivedFunctor Λ Y).obj A)) :=
  (derivedPullComparison Λ' f).inv.app ((scalarProjectionExtension a Y).obj A) ≫
    (derivedFunctor Λ' X).map ((CondensedRing.derivedPullIso a f).inv.app A) ≫
    (d X).derivedExtension.hom.app ((internalDerivedPullback Λ f).obj A) ≫
    (d X).sectionPair.derived.map ((derivedPullComparison Λ f).hom.app A)

/-- The cartesian regular-coefficient arrow in the section model.
Source: Stacks 03EL (blueprint: lem-sfb-internal-scalar-projection-mate). -/
def scalarProjectionSectionCoefficientPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj
        ((derivedFunctor Λ Y).obj (scalarProjectionDerivedCoefficient a Y)) ⟶
      (derivedFunctor Λ X).obj (scalarProjectionDerivedCoefficient a X) :=
  (derivedPullComparison Λ f).inv.app (scalarProjectionDerivedCoefficient a Y) ≫
    (derivedFunctor Λ X).map (scalarProjectionDerivedCoefficientPull a f)

/-- The specified h and derivedPullIso agree with section-ring scalar tensor and pullback.
Source: Stacks 03EL, 06YY and 07A4
(blueprint: lem-sfb-internal-scalar-projection-mate). -/
def ScalarProjectionSectionTensorTransport
    (d : ∀ T : Scheme.{u}, ScalarProjectionSectionIdentifications a T)
    (h : ∀ T : Scheme.{u},
      scalarProjectionExtension a T ⋙ scalarProjectionRestriction a T ≅
        (CondensedRing.derivedTensor Λ T).obj (scalarProjectionDerivedCoefficient a T))
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ k : ∀ T : Scheme.{u},
    (d T).sectionPair.derived ⋙
        scalarProjectionSectionDerivedRestriction a T ≅
      (Functor.curry.obj (tensor Λ T)).obj
        ((derivedFunctor Λ T).obj (scalarProjectionDerivedCoefficient a T)),
  (∀ (T : Scheme.{u}) (A : DerivedCategory (internalModules Λ T)),
    (k T).hom.app ((derivedFunctor Λ T).obj A) =
      (scalarProjectionSectionDerivedRestriction a T).map
          ((d T).derivedExtension.inv.app A) ≫
        (d T).derivedRestriction.inv.app ((scalarProjectionExtension a T).obj A) ≫
        (derivedFunctor Λ T).map ((h T).hom.app A) ≫
        (tensorComparison Λ T).hom.app (scalarProjectionDerivedCoefficient a T, A)) ∧
  (∀ A : DerivedCategory (internalModules Λ Y),
    (derivedPullback Λ f).map ((k Y).inv.app ((derivedFunctor Λ Y).obj A)) ≫
      (derivedPullback Λ f).map
        ((scalarProjectionSectionDerivedRestriction a Y).map
          ((d Y).derivedExtension.inv.app A)) ≫
      scalarProjectionSectionRestrictionPull a d f ((scalarProjectionExtension a Y).obj A) ≫
      (scalarProjectionSectionDerivedRestriction a X).map
        (scalarProjectionSectionPull a d f A) ≫
      (k X).hom.app ((derivedPullback Λ f).obj ((derivedFunctor Λ Y).obj A)) =
    (tensorPullComparison Λ f).hom.app
        ((derivedFunctor Λ Y).obj (scalarProjectionDerivedCoefficient a Y),
          (derivedFunctor Λ Y).obj A) ≫
      (tensor Λ X).map (Prod.mkHom (scalarProjectionSectionCoefficientPull a f)
        (𝟙 ((derivedPullback Λ f).obj ((derivedFunctor Λ Y).obj A)))))

/-- Full normalization of the scalar projection mate, with its actual internal origin.
Source: blueprint lem-sfb-dc-lower-star-preserves.proof.md, last paragraph; Stacks 0B56
(blueprint: lem-sfb-internal-scalar-projection-mate).

Proof:
1. Apply lem-pe-internal-section-tensor-comparison on both sites and for both rings.
   Exactness identifies acyclicity, flatness, signed sum-total tensors and K-flat tests.
   Apply lem-pd-section-derived-pushpull-normalization to transport K-injectives,
   resolutions, geometric adjunctions, their units and their counits. Apply
   lem-pd-section-derived-tensor-normalization for the localized tensor arrows.
2. Apply lem-sfb-internal-section-scalar-adjunction to each coefficient map. Its
   restriction comparison is identity on sections; its extension comparison fixes
   balanced generators, scalar units, counits and derived transposes. The canonical
   scalar pullback arrow is the localized balanced arrow of
   lem-sfb-kflat-scalar-comparison-normalization.
3. The coefficient squares commute by sk-def-sfb-coefficient-change. Apply
   lem-weil-pbc-ring-sheaf-change-adjunction for the specified comparison d and its
   transpose identity. The section geometric adjunctions agree with those of
   def-weil-pbc-proetale-operations by the unique derived bijection of
   lem-pc-pre-derived-adjoint-functors-general. Restriction is conservative.
4. The ordinary scalar tensor comparison sends s tensor m to the same balanced
   generator. Resolve by lem-pc-kflat-resolution and localize, giving h with the
   displayed comparison square and naturality on all derived morphisms.
5. On balanced generators the scalar pullback arrow and geometric tensor arrow both
   pull back s tensor m to the two pulled-back factors. Their equality follows by
   the sheaf tensor universal property; it survives signed totals and localization.
6. Put A=G_R C. The S-adjunct of gamma is the inverse of derivedPullIso followed by
   T_X(epsilon_R). Transpose its restriction using step 3. Steps 4 and 5 identify
   that transpose with the tensor comparison followed by 1 tensor epsilon_R,
   with the cartesian coefficient identification. Adjunction injectivity identifies
   the specified maps. Finally apply the fixed section functor and its geometric
   and tensor comparison isomorphisms. No projection-formula invertibility is used.
-/
theorem internal_scalar_projection_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ e : ∀ T : Scheme.{u},
      Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a T) ⋙
          Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a T) ≅
        tensorLeft (scalarProjectionCoefficient a T),
    (∀ (T : Scheme.{u}) (M : internalModules Λ T) (W : T.ProEtᵒᵖ)
      (s : (condensedRingObj Λ' T).obj.obj W) (m : M.X.obj.obj W),
      ((e T).hom.app M).hom.hom.app W
        (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
          (AlgebraicGeometry.ProEtale.coefficientMap a T) M W s m) =
        internalPureTensor Λ T (scalarProjectionCoefficient a T) M W s m) ∧
    ∃ h : ∀ T : Scheme.{u},
      scalarProjectionExtension a T ⋙ scalarProjectionRestriction a T ≅
        (CondensedRing.derivedTensor Λ T).obj (scalarProjectionDerivedCoefficient a T),
    ScalarProjectionDerivedTensorNormalization a e h ∧
    ∃ d : ∀ T : Scheme.{u}, ScalarProjectionSectionIdentifications a T,
    ScalarProjectionSectionTensorTransport a d h f ∧
    (scalarProjectionRestriction a Y).ReflectsIsomorphisms ∧
    ScalarProjectionPullTransport a f h ∧
    (∀ C : DerivedCategory (internalModules Λ X),
      (scalarProjectionInternalAdjunction Λ' f).homEquiv _ _
        ((CondensedRing.derivedPullIso a f).inv.app
            ((internalDerivedPushforward Λ f).obj C) ≫
          (scalarProjectionExtension a X).map
            ((scalarProjectionInternalAdjunction Λ f).counit.app C)) =
        (CondensedRing.derivedPushHom a f).app C) ∧
    (∀ C : DerivedCategory (internalModules Λ X),
      (derivedFunctor Λ Y).map
        ((h Y).inv.app ((internalDerivedPushforward Λ f).obj C) ≫
          (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a Y)).mapDerivedCategory.map
            ((CondensedRing.derivedPushHom a f).app C) ≫
          (CondensedRing.derivedComapLowerStarIso a f).hom.app
            ((scalarProjectionExtension a X).obj C) ≫
          (internalDerivedPushforward Λ f).map ((h X).hom.app C)) =
        (derivedFunctor Λ Y).map (scalarProjectionCounitMate a f C))
    := by sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
