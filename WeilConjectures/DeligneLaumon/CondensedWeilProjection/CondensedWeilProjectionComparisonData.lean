/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation.TowerRightDerivedEvaluation
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! # Normalized tensor and projection data for condensed Weil modules

Source: latest blueprint, lem-fix-weil-operations.proof.md, tensor/pullback paragraph
and final paragraph (ordinary adjunction and the tensor/counit projection composite);
Stacks Project, Tags 03EL, 0943 and 0B56.
(blueprint: def-sf-native-proper-projection-comparison-data)

The ambient records are formed on actual module categories for schemes with
automorphisms, then specialized to geometric Frobenius on the finite-field fibres.
A presentation is specified data, not an existence assertion. Its ordinary tensor
is fixed by the relative module tensor and diagonal Frobenius structure. All totals
keep the left degree first and use the Koszul differential. The comparison records
below do not assert invertibility of the projection morphism.

## Main definitions

* `TensorPresentation`: the fixed diagonal relative tensor and its K-flat presentation.
* `ForgetTensorComparison`: cochain and derived forgetting with summand normalization.
* `ComparisonData`: the induced adjunction, pullback tensor map, and normalized comparisons.
* `projectionMap`: the tensor/counit adjunction transpose on the stated source and target.
* `ordinaryProjectionMap`: the recorded ordinary module-object projection arrow.
* `nativeProperProjectionComparisonData`: specialization to the prescribed finite-field datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096

universe u uA vA wA uB vB wB uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeilProjection

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}} (g : Aut T)

/-- The actual condensed module category on the geometric fibre.
Source: coefficient convention (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The actual category of modules with invertible geometric-Frobenius structure.
Source: Weil-module paragraph (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev WeilModules := condensedWeilModules Λ g.hom

/-- Exact Frobenius forgetting, before localization.
Source: forgetting paragraph (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev forget := condensedWeilModuleForget Λ
  g.hom

/-- Termwise exact Frobenius forgetting.
Source: forgetting paragraph (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev forgetCh := (forget Λ g).mapHomologicalComplex (.up ℤ)

/-- Forgetting on the ordinary unbounded derived categories.
Source: forgetting paragraph (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev forgetD := (forget Λ g).mapDerivedCategory

/-- The canonical localization factor of exact forgetting, with the stated direction.
Source: Stacks 015F (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev forgetFactor := (forget Λ g).mapDerivedCategoryFactors

set_option maxHeartbeats 1600000 in
-- The concrete module categories have large instance expressions.
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve their colimit and additive instances once per declaration.
section Tensor

variable [t : TensorPresentation Λ g]
local instance : MonoidalCategory (WeilModules Λ g) := t.monoidal
local instance : MonoidalPreadditive (WeilModules Λ g) := t.preadditive

set_option maxHeartbeats 1600000 in
-- Building the total requires colimits in the concrete Weil category.
set_option synthInstance.maxHeartbeats 200000 in
-- The colimit instance has a large concrete category expression.
/-- The signed direct-sum total of the fixed ordinary diagonal relative tensor.
Source: total-tensor paragraph (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev total := (curriedTensor (WeilModules Λ g)).map₂CochainComplex

set_option synthInstance.maxHeartbeats 200000 in
-- Reuse the total in the concrete Weil category.
/-- The computation isomorphism Q Tot(P,Q) ≅ QP ⊗ᴸ Q, the inverse derived counit.
Source: specified K-flat presentation
(blueprint: def-sf-native-proper-projection-comparison-data). -/
def computation (P Q : CochainComplex (WeilModules Λ g) ℤ)
    (hP : P.IsKFlatForTotalTensor) (hQ : Q.IsKFlatForTotalTensor) :
    DerivedCategory.Q.obj (((total Λ g (t := t)).obj P).obj Q) ≅
      (t.derived.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) :=
  letI := t.computation_isIso P Q hP hQ
  (asIso ((t.derivedCounit.app P).app Q)).symm

set_option maxHeartbeats 1600000 in
-- The concrete module categories have large instance expressions.
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve their colimit and additive instances once per declaration.
/-- A normalized forgetting tensor comparison: natural cochain and derived
isomorphisms, the identity on each internal relative-tensor summand, preservation
of K-flatness, and precisely the localization normalization in the node.
The inverse lax localization map is the ordinary computation map mᴬ; expressing
the equation with the lax map avoids choosing a second computation isomorphism.
Source: displayed tau equation and summand clause
(blueprint: def-sf-native-proper-projection-comparison-data). -/
structure ForgetTensorComparison where
  cochain : (Functor.postcompose₂.obj (forgetCh Λ g)).obj (total Λ g (t := t)) ≅
    (((Functor.whiskeringLeft₂ _).obj (forgetCh Λ g)).obj
      (forgetCh Λ g)).obj (curriedTensor (Modules Λ T)).map₂CochainComplex
  summand (P Q : CochainComplex (WeilModules Λ g) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    HEq ((forget Λ g).map (HomologicalComplex.ιTensorObj P Q i j n h) ≫
      (((cochain.hom.app P).app Q).f n))
      (HomologicalComplex.ιTensorObj ((forgetCh Λ g).obj P)
        ((forgetCh Λ g).obj Q) i j n h)
  preservesKFlat (P : CochainComplex (WeilModules Λ g) ℤ)
    (hP : P.IsKFlatForTotalTensor) :
    CochainComplex.IsKFlatForTotalTensor ((forgetCh Λ g).obj P)
  derived : (Functor.postcompose₂.obj (forgetD Λ g)).obj t.derived ≅
    (((Functor.whiskeringLeft₂ _).obj (forgetD Λ g)).obj
      (forgetD Λ g)).obj
        (CondensedRing.derivedTensor Λ T)
  normalization (P Q : CochainComplex (WeilModules Λ g) ℤ)
    (hP : P.IsKFlatForTotalTensor) (hQ : Q.IsKFlatForTotalTensor) :
    (forgetD Λ g).map (computation Λ g (t := t) P Q hP hQ).hom ≫
      (derived.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
      ((forgetFactor Λ g).hom.app P ⊗ₘ
        (forgetFactor Λ g).hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((forgetCh Λ g).obj P) ((forgetCh Λ g).obj Q) =
    (forgetFactor Λ g).hom.app (((total Λ g (t := t)).obj P).obj Q) ≫
      DerivedCategory.Q.map ((cochain.hom.app P).app Q)

end Tensor

end WeilConjectures.CondensedWeilProjection

namespace WeilConjectures.CondensedWeilProjection

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  upperStarFromPoint Endofunctor.IsoAlgebra.mapOfNatIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  nativeWeilPullbackForget CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  CondensedRing.derivedUpperStarLowerStarAdjunction

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

/-- The termwise module counit, with its two cochain functors explicit.
Source: lifted module adjunction
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def cochainAdjunctionCounit
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    (L : B ⥤ A) [L.Additive] (R : A ⥤ B) [R.Additive] (a : L ⊣ R)
    (I : CochainComplex A ℤ) :
    (L.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj I) ⟶ I :=
  (a.mapHomologicalComplex (.up ℤ)).counit.app I

/-- The derived counit comes from the actual module counit and computation unit.
The equation is formed before specializing either abelian category.
Source: induced-adjunction paragraph
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def DerivedAdjunctionIsInduced
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (L : B ⥤ A) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : A ⥤ B) [R.Additive]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (a₀ : L ⊣ R) (a : L.mapDerivedCategory ⊣ R.rightDerivedFunctorOfQuasiIsoResolutions h) :
    Prop :=
  ∀ I : CochainComplex A ℤ,
    L.mapDerivedCategory.map (TowerRightDerivedEvaluation.cochainUnit R h I) ≫
        a.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (cochainAdjunctionCounit L R a₀ I)

/-- A cochain tensor comparison is the signed total of its degreewise map.
The predicate is checked abstractly to keep the concrete scheme limits opaque.
Source: signed-total paragraph
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def CochainTensorComparisonSummands
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasColimitsOfSize.{0, 0} A]
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    [MonoidalCategory B] [MonoidalPreadditive B] [HasColimitsOfSize.{0, 0} B]
    (L : A ⥤ B) [L.Additive]
    (s : (Functor.postcompose₂.obj L).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj (curriedTensor B))
    (sCh : (Functor.postcompose₂.obj (L.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor A).map₂CochainComplex ≅
      (((Functor.whiskeringLeft₂ _).obj (L.mapHomologicalComplex (.up ℤ))).obj
        (L.mapHomologicalComplex (.up ℤ))).obj (curriedTensor B).map₂CochainComplex) : Prop :=
  ∀ (P Q : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n),
    L.map (HomologicalComplex.ιTensorObj P Q i j n h) ≫ (((sCh.hom.app P).app Q).f n) =
      (s.hom.app (P.X i)).app (Q.X j) ≫
        HomologicalComplex.ιTensorObj
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj Q) i j n h

/-- The pullback tensor map is induced with the specified total-derived counits.
Source: total-left-derived-comparison paragraph
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def DerivedPullTensorNormalization
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasColimitsOfSize.{0, 0} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [HasColimitsOfSize.{0, 0} B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (TA : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (TB : DerivedCategory B ⥤ DerivedCategory B ⥤ DerivedCategory B)
    (eA : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj TA ⟶
      (Functor.postcompose₂.obj DerivedCategory.Q).obj (curriedTensor A).map₂CochainComplex)
    (eB : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj TB ⟶
      (Functor.postcompose₂.obj DerivedCategory.Q).obj (curriedTensor B).map₂CochainComplex)
    (tCh : (Functor.postcompose₂.obj (L.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor A).map₂CochainComplex ≅
      (((Functor.whiskeringLeft₂ _).obj (L.mapHomologicalComplex (.up ℤ))).obj
        (L.mapHomologicalComplex (.up ℤ))).obj (curriedTensor B).map₂CochainComplex)
    (mu : (Functor.postcompose₂.obj L.mapDerivedCategory).obj TA ≅
      (((Functor.whiskeringLeft₂ _).obj L.mapDerivedCategory).obj L.mapDerivedCategory).obj TB) :
    Prop :=
  ∀ (P Q : CochainComplex A ℤ),
    (mu.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        (TB.map (L.mapDerivedCategoryFactors.hom.app P)).app _ ≫
        (TB.obj _).map (L.mapDerivedCategoryFactors.hom.app Q) ≫
        (eB.app ((L.mapHomologicalComplex (.up ℤ)).obj P)).app
          ((L.mapHomologicalComplex (.up ℤ)).obj Q) =
      L.mapDerivedCategory.map ((eA.app P).app Q) ≫
        L.mapDerivedCategoryFactors.hom.app (((curriedTensor A).map₂CochainComplex.obj P).obj Q) ≫
        DerivedCategory.Q.map ((tCh.hom.app P).app Q)

/-- Direct-image forgetting is normalized by the actual right-derived cochain units.
No preservation of K-injectivity by forgetting is assumed.
Source: displayed K-injective unit equation
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def ForgetRightUnitNormalization
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {E : Type uD} [Category.{vD} E] [Abelian E] [HasDerivedCategory.{wD} E]
    [Abelian.HasKInjectiveResolutions C]
    (FW : A ⥤ B) [FW.Additive]
    (hW : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (FA : C ⥤ E) [FA.Additive]
    (UZ : A ⥤ C) [UZ.Additive] [PreservesFiniteLimits UZ] [PreservesFiniteColimits UZ]
    (UY : B ⥤ E) [UY.Additive] [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
    (sCh : FW.mapHomologicalComplex (.up ℤ) ⋙ UY.mapHomologicalComplex (.up ℤ) ≅
      UZ.mapHomologicalComplex (.up ℤ) ⋙ FA.mapHomologicalComplex (.up ℤ))
    (b : FW.rightDerivedFunctorOfQuasiIsoResolutions hW ⋙ UY.mapDerivedCategory ≅
      UZ.mapDerivedCategory ⋙ FA.rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex A ℤ) (_hI : I.IsKInjective),
    UY.mapDerivedCategory.map (TowerRightDerivedEvaluation.cochainUnit FW hW I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        FA.rightDerivedFunctor.map (UZ.mapDerivedCategoryFactors.hom.app I) =
      UY.mapDerivedCategoryFactors.hom.app ((FW.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (sCh.hom.app I) ≫
        (derivedCochainRightUnit FA FA.rightDerivedFunctor FA.rightDerivedFunctorUnit).app
          ((UZ.mapHomologicalComplex (.up ℤ)).obj I)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {Z Y : Scheme.{u}}
  (gZ : Aut Z) (gY : Aut Y) (p : Z ⟶ Y) (sq : CommSq gZ.hom p p gY.hom)

/-- The actual lifted module pullback of the geometric base change.
Source: native framework (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev pull₀ : WeilModules Λ gY ⥤ WeilModules Λ gZ :=
  nativeWeilModulePullback Λ
  gZ gY p
  sq

/-- The actual lifted module direct image of the geometric base change.
Source: native framework (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev push₀ : WeilModules Λ gZ ⥤ WeilModules Λ gY :=
  nativeWeilModuleDirectImage Λ
  gZ gY p
  sq

/-- Exact localized Weil pullback, on the full unbounded derived categories.
Source: native framework (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev pull : DerivedCategory (WeilModules Λ gY) ⥤
    DerivedCategory (WeilModules Λ gZ) :=
  (pull₀ Λ gZ gY p sq).mapDerivedCategory

/-- Total right derivation of the actual Weil module direct image.
Source: native framework (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev push : DerivedCategory (WeilModules Λ gZ) ⥤
    DerivedCategory (WeilModules Λ gY) :=
  (push₀ Λ gZ gY p sq).rightDerivedFunctorOfQuasiIsoResolutions (nativeWeilResolutions _)

/-- Ordinary pullback is the recorded K-flat total left-derived functor.
Source: module push/pull adjunction
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev ordinaryPull :=
  (CondensedRing.upperStar Λ p).leftDerivedFunctor

/-- Ordinary direct image is the recorded total right-derived functor.
Source: module push/pull adjunction
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev ordinaryPush :=
  (CondensedRing.lowerStar Λ p).rightDerivedFunctor

/-- The sheaf direct-image comparison, identity on the actual underlying module objects.
Source: direct-image normalization paragraph
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def pushForget₀ : push₀ Λ gZ gY p sq ⋙ forget Λ gY ≅
    forget Λ gZ ⋙ CondensedRing.lowerStar Λ
      p :=
  Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
    (asIso (CondensedRing.lowerStarBaseChange Λ
      sq))

/-- Its termwise cochain comparison, including the functor-composition factors.
Source: direct-image normalization paragraph
(blueprint: def-sf-native-proper-projection-comparison-data). -/
@[irreducible] def pushForgetCh :
    (push₀ Λ gZ gY p sq).mapHomologicalComplex (.up ℤ) ⋙ forgetCh Λ gY ≅
      forgetCh Λ gZ ⋙
        (CondensedRing.lowerStar Λ
          p).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (pushForget₀ Λ gZ gY p sq) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (forget Λ gZ ⋙ CondensedRing.lowerStar Λ
        p)) (.up ℤ)).symm

variable [tZ : TensorPresentation Λ gZ] [tY : TensorPresentation Λ gY]
local instance : MonoidalCategory (WeilModules Λ gZ) := tZ.monoidal
local instance : MonoidalCategory (WeilModules Λ gY) := tY.monoidal
local instance : MonoidalPreadditive (WeilModules Λ gZ) := tZ.preadditive
local instance : MonoidalPreadditive (WeilModules Λ gY) := tY.preadditive

set_option maxHeartbeats 1600000 in
-- The concrete module categories have large instance expressions.
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve their colimit and additive instances once per declaration.
/-- The normalized projection-comparison record on the fixed actual functors.
The sheaf pullback comparison is the ordinary relative module tensor map, and
its cochain comparison is characterized on every left-first summand. The derived
comparison is characterized by the two tensor-derived counits and the exact
pullback localization factor, on all cochain pairs. This is its total left-derived
normalization, with no arbitrary replacement tensor operations.

The last two equations are the counit compatibility and the displayed
K-injective computation-unit compatibility. No inhabitant is asserted.
Source: lem-fix-weil-operations, ordinary adjunction paragraph; Stacks 03EL, 0943, 0B56
(blueprint: def-sf-native-proper-projection-comparison-data). -/
structure ComparisonData where
  tensorZ : ForgetTensorComparison Λ gZ (t := tZ)
  tensorY : ForgetTensorComparison Λ gY (t := tY)
  /-- The actual lifted module adjunction, normalized by faithful sheaf forgetting. -/
  moduleAdjunction : pull₀ Λ gZ gY p sq ⊣ push₀ Λ gZ gY p sq
  moduleCounit_normalization (M : WeilModules Λ gZ) :
    HEq ((forget Λ gZ).map (moduleAdjunction.counit.app M))
      ((CondensedRing.upperStarLowerStarAdjunction Λ
        p).counit.app M.carrier)
  /-- Derived adjunction on the actual Weil pullback and direct image. -/
  adjunction : pull Λ gZ gY p sq ⊣ push Λ gZ gY p sq
  /-- Its counit is induced from the termwise module counit and actual derived unit. -/
  adjunction_induced :
    DerivedAdjunctionIsInduced (pull₀ Λ gZ gY p sq) (push₀ Λ gZ gY p sq)
      (nativeWeilResolutions _) moduleAdjunction adjunction
  /-- Ordinary module pullback tensor comparison, with the diagonal Weil maps. -/
  sheafTensor :
    (Functor.postcompose₂.obj (pull₀ Λ gZ gY p sq)).obj (curriedTensor (WeilModules Λ gY)) ≅
      (((Functor.whiskeringLeft₂ _).obj (pull₀ Λ gZ gY p sq)).obj
        (pull₀ Λ gZ gY p sq)).obj (curriedTensor (WeilModules Λ gZ))
  sheafTensor_normalization (M N : WeilModules Λ gY) :
    HEq ((forget Λ gZ).map ((sheafTensor.hom.app M).app N))
      (Functor.OplaxMonoidal.δ
        (CondensedRing.upperStar Λ p)
        M.carrier N.carrier)
  /-- The signed total of the sheaf comparison, with the left degree first. -/
  cochainTensor :
    (Functor.postcompose₂.obj ((pull₀ Λ gZ gY p sq).mapHomologicalComplex (.up ℤ))).obj
      (total Λ gY (t := tY)) ≅
      (((Functor.whiskeringLeft₂ _).obj ((pull₀ Λ gZ gY p sq).mapHomologicalComplex (.up ℤ))).obj
        ((pull₀ Λ gZ gY p sq).mapHomologicalComplex (.up ℤ))).obj (total Λ gZ (t := tZ))
  cochainTensor_summand :
    CochainTensorComparisonSummands (pull₀ Λ gZ gY p sq) sheafTensor cochainTensor
  /-- The normalized total left-derived pullback tensor comparison. -/
  pullTensor : (Functor.postcompose₂.obj (pull Λ gZ gY p sq)).obj tY.derived ≅
    (((Functor.whiskeringLeft₂ _).obj (pull Λ gZ gY p sq)).obj
      (pull Λ gZ gY p sq)).obj tZ.derived
  pullTensor_normalization :
    DerivedPullTensorNormalization (pull₀ Λ gZ gY p sq) tY.derived tZ.derived
      tY.derivedCounit tZ.derivedCounit cochainTensor pullTensor
  /-- Forgetting the actual pullback to the specified ordinary left-derived pullback. -/
  pullForget : pull Λ gZ gY p sq ⋙ forgetD Λ gZ ≅
    forgetD Λ gY ⋙ ordinaryPull Λ p
  /-- Fix its canonical exact-functor localization normalization. -/
  pullForget_normalization : pullForget =
    nativeWeilPullbackForget Λ gZ
      gY p sq ≪≫
      Functor.isoWhiskerLeft (forgetD Λ gY)
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ
          p).symm
  /-- Forgetting direct image to the specified ordinary total right-derived functor. -/
  pushForget : push Λ gZ gY p sq ⋙ forgetD Λ gY ≅
    forgetD Λ gZ ⋙ ordinaryPush Λ p
  /-- The actual derived counit agrees after forgetting and the two comparisons. -/
  counit_normalization (A : DerivedCategory (WeilModules Λ gZ)) :
    (forgetD Λ gZ).map (adjunction.counit.app A) =
      pullForget.hom.app ((push Λ gZ gY p sq).obj A) ≫
      (ordinaryPull Λ p).map (pushForget.hom.app A) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
        p).counit.app ((forgetD Λ gZ).obj A)
  /-- The direct-image comparison uses the actual right-derived computation units. -/
  rightUnit_normalization :
    ForgetRightUnitNormalization (push₀ Λ gZ gY p sq) (nativeWeilResolutions _)
      (CondensedRing.lowerStar Λ p) (forget Λ gZ) (forget Λ gY)
      (pushForgetCh Λ gZ gY p sq) pushForget

omit tZ tY in
end WeilConjectures.CondensedWeilProjection
