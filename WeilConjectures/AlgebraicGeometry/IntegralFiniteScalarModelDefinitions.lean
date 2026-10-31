/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.Topology.ProfiniteSectionsFiniteQuotient
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.Algebra.Homology.FiniteFreeMonoCokernelKFlat
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # The integral-to-finite perfect scalar model

Source: current blueprint, scalar-six direct-image proof, finite free and finitely
presented coefficient extensions and formal properties
(blueprint: lem-sfb-integral-finite-scalar-perfect-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar

open CondensedRing

/-- The existing internal module category at the profinite point.
Source: blueprint finite free resolution
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
abbrev PointModules (Λ : ScalarSixRing.{u}) :=
  Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X

/-- Exact strong monoidal pullback of modules from the point.
Source: blueprint pulling back the square free resolution
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
abbrev pointPull (Λ : ScalarSixRing.{u}) (Z : Scheme.{u}) :=
  (sfbPullbackFromPoint Z).mapMod Λ.X

/-- Additivity of the existing point direct image, which is precomposition.
Source: blueprint point inverse-image adjunction
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
instance pointRightAdditive : pointLowerStar.{u}.Additive where
  map_add := rfl

/-- The existing strong monoidal and braided structures bundled together.
Source: blueprint monoidal comparison
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
instance pointBraided (Z : Scheme.{u}) : (sfbPullbackFromPoint Z).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

/-- Additivity inherited from the existing point/geometric adjunction.
Source: blueprint exact point inverse image
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
instance pointAbAdditive (Z : Scheme.{u}) : (sfbPullbackFromPoint Z).Additive :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).left_adjoint_additive

/-- Additivity of point pullback, read on the faithful underlying abelian sheaves.
Source: blueprint exact point inverse image
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
instance pointPull_additive (Λ : ScalarSixRing.{u}) (Z : Scheme.{u}) :
    (pointPull Λ Z).Additive where
  map_add {_X _Y f g} := Mod.hom_ext _ _
    ((sfbPullbackFromPoint Z).map_add (f := f.hom) (g := g.hom))

/-- The specified two-term cone, pulled back from the point degreewise.
Source: blueprint two-term model in degrees -1,0
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def complex (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ))
    (Z : Scheme.{u}) :=
  ((pointPull Λ Z).mapHomologicalComplex (.up ℤ)).obj
    (CochainComplex.monoCokernelComplex S.f)

/-- Its degree-zero target, also pulled back degreewise.
Source: blueprint augmentation to A_Z[0]
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def target (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ))
    (Z : Scheme.{u}) :=
  ((pointPull Λ Z).mapHomologicalComplex (.up ℤ)).obj
    ((CochainComplex.singleFunctor _ 0).obj S.X₃)

/-- Pullback of the actual quotient augmentation.
Source: blueprint specified q_Z
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def augmentation (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ))
    (Z : Scheme.{u}) : complex Λ S Z ⟶ target Λ S Z :=
  ((pointPull Λ Z).mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.monoCokernelAugmentation S)

/-- The canonical adjunction with the exact, termwise inverse image as left adjoint.
Source: blueprint ordinary unbounded geometric adjunction
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def geometricAdjunction (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⊣ moduleObjectDerivedPushforward Λ.X f :=
  (derivedUpperStarLowerStarAdjunction Λ.X f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)

/-- The tensor comparison of that exact pullback, with its canonical derived normalization.
Source: blueprint monoidal pullback comparison
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def tensorPull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPull Λ f).obj (B ⊗ K) ⟶
      (scalarSixPull Λ f).obj B ⊗ (scalarSixPull Λ f).obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv.app (B ⊗ K) ≫
    (((CondensedRing.upperStar Λ.X f).leftDerivedTensorComparison).app B).app K ≫
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app B ⊗ₘ
        (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app K)

/-- The actual coefficient-change mate, defined with the inverse of the normalized
pullback comparison and the actual geometric counit.
Source: blueprint formal properties, definition of gamma
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def gamma (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
  (geometricAdjunction Λ' f).homEquiv _ _
    ((D.theta a f).inv.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
      (scalarSixChange a X).map ((geometricAdjunction Λ f).counit.app K))

/-- Exact derived restriction for the point-induced scalar map.
Source: blueprint scalar restriction (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
abbrev restriction {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ'.X Z) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z) :=
  (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapDerivedCategory

/-- The actual scalar adjunction, including its normalized unit and counit.
Source: blueprint scalar adjunction (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
abbrev scalarAdjunction {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)

/-- The canonical restriction/direct-image comparison, obtained by conjugating the
normalized pullback/scalar comparison under the two composite adjunctions.
Source: blueprint formal properties (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def restrictionPush (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPushforward Λ'.X f ⋙ restriction a Y ≅
      restriction a X ⋙ moduleObjectDerivedPushforward Λ.X f :=
  conjugateIsoEquiv ((scalarAdjunction a Y).comp (geometricAdjunction Λ' f))
    ((geometricAdjunction Λ f).comp (scalarAdjunction a X)) (D.theta a f)

/-- A continuous commutative coefficient ring, using the existing continuous-section ring.
Source: blueprint condensed coefficients
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
abbrev condensed (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] :
    ScalarSixRing.{u} := CommMon.mk (Profinite.continuousCoefficientRingObj O)

/-- The existing postcomposition homomorphism, bundled as a commutative ring-object map.
Source: blueprint a and a_Z (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def condensedMap {O A : Type u} [CommRing O] [CommRing A]
    [TopologicalSpace O] [TopologicalSpace A] [IsTopologicalRing O] [IsTopologicalRing A]
    (a : O →+* A) (ha : Continuous a) : condensed O ⟶ condensed A :=
  let f : Profinite.continuousCoefficientRingObj O ⟶
      Profinite.continuousCoefficientRingObj A :=
    Profinite.continuousMapRingObjMapOfUniverse.{u, u} a ha
  letI : IsMonHom f := by
    exact Profinite.isMonHom_continuousMapRingObjMapOfUniverse a ha
  CommMon.homMk (Mon.Hom.mk f)

/-- Pullback of the restricted regular coefficient module is the restricted regular
module on the scheme, via the standard mapMod/comap and unit comparisons.
Source: blueprint A_Z (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def coefficientModuleIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :
    (pointPull Λ Z).obj ((Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) ≅
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        (Mod.regular (condensedRingObj Λ'.X Z)) :=
  ((sfbPullbackFromPoint Z).mapModComapIso (R := Λ.X) (S := Λ'.X) a.hom.hom).app
    (Mod.regular Λ'.X) ≪≫
    (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapIso
      ((sfbPullbackFromPoint Z).mapModUnitIso (R := Λ'.X)).symm

/-- The scalar-first projection map, defined by the tensor comparison and O-counit.
Source: blueprint projection formula (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def projection (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (e : (scalarSixPull Λ f).obj B ≅ P)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
  (geometricAdjunction Λ f).homEquiv _ _
    (tensorPull Λ f B ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
      (e.hom ⊗ₘ (geometricAdjunction Λ f).counit.app K))

/-- The degree-zero coefficient identification supplied by the chosen point quotient.
Source: blueprint quotient augmentation
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def targetZeroIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u}) :
    (target Λ S Z).X 0 ≅
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        (Mod.regular (condensedRingObj Λ'.X Z)) :=
  (pointPull Λ Z).mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃) ≪≫
    (pointPull Λ Z).mapIso t ≪≫ coefficientModuleIso a Z

/-- The derived-to-ordinary scalar counit on a complex, retaining the localization
comparisons instead of choosing an unspecified scalar comparison.
Source: blueprint computation on K-flat representatives
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def scalarCounit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u})
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ) :
    (scalarSixChange a Z).obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj
        (((Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom Z)).mapHomologicalComplex
          (.up ℤ)).obj C) :=
  (scalarSixChange a Z).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom Z)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The explicit ordinary augmentation normalization for a proposed derived beta.
The ordinary extension comparison is fixed on underlying abelian sheaves, and the
signed direct-sum total comparison is fixed on its (0,n) summands. Thus this condition
cannot hold for an arbitrary isomorphism with the same endpoints.
Source: blueprint resolving-class computation
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def AugmentationNormalized {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u})
    (β : tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z) : Prop :=
  ∃ κ : ∀ M : ModuleRingedComparison.internalModules Λ.X Z,
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        (Mod.regular (condensedRingObj Λ'.X Z)) ⊗ M ≅
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj
        ((Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).obj M),
    (∀ M, (κ M).hom.hom =
      (Mod.extendForgetTensorObjIso (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z) M).inv) ∧
    ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
      ∃ τ : HomologicalComplex.tensorObj (target Λ S Z) C ≅
          (((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
            a.hom.hom Z)).mapHomologicalComplex (.up ℤ)).obj
            (((Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
              a.hom.hom Z)).mapHomologicalComplex
              (.up ℤ)).obj C)),
        (∀ n : ℤ,
          HomologicalComplex.ιTensorObj (target Λ S Z) C 0 n n (zero_add n) ≫ τ.hom.f n =
            ((targetZeroIso a S t Z).hom ⊗ₘ 𝟙 (C.X n)) ≫ (κ (C.X n)).hom) ∧
        β.hom.app (DerivedCategory.Q.obj C) ≫
            (restriction a Z).map (scalarCounit a Z C) ≫
            (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
              a.hom.hom Z)).mapDerivedCategoryFactors.hom.app _ =
          Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C ≫
            DerivedCategory.Q.map
              (HomologicalComplex.tensorHom (augmentation Λ S Z) (𝟙 C)) ≫
            DerivedCategory.Q.map τ.hom

/-- Canonical module comparison induced by upperStarFromPointComp, with its specified
extension-of-scalars unit, so it retains the monoidal point-pullback normalization.
Source: blueprint p_X = f* p_Y (blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def pointModuleComp (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pointPull Λ Y ⋙ CondensedRing.upperStar Λ.X f ≅ pointPull Λ X :=
  Functor.mapModCompExtendScalarsIso (sfbPullbackFromPoint Y)
    (ProEtale.upperStar Ab.{u + 1} f) (upperStarFromPointComp f).hom Λ.X

/-- The same specified point comparison on complexes, before localization.
Source: blueprint inverse-image compatibility
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def pointComplexComp (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (PointModules Λ) ℤ) :
    ((CondensedRing.upperStar Λ.X f).mapHomologicalComplex (.up ℤ)).obj
      (((pointPull Λ Y).mapHomologicalComplex (.up ℤ)).obj C) ≅
    ((pointPull Λ X).mapHomologicalComplex (.up ℤ)).obj C :=
  (Functor.mapHomologicalComplexCompIso (pointModuleComp Λ f) (.up ℤ)).app C

/-- Localization of the specified complex comparison, using exact geometric pullback.
Source: blueprint compatibility in D(O)
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def modelPull (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarSixPull Λ f).obj (DerivedCategory.Q.obj (complex Λ S Y)) ≅
      DerivedCategory.Q.obj (complex Λ S X) :=
  (CondensedRing.upperStar Λ.X f).mapDerivedCategoryFactors.app (complex Λ S Y) ≪≫
    DerivedCategory.Q.mapIso (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f))

/-- The full derived assertions for one specified square resolution. Both inverse-image
and direct-image equations refer to the actual normalized comparisons, not to witnesses
with unspecified maps.
Source: blueprint finite perfect model and formal properties
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def DerivedAssertions (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) : Prop :=
  (∀ Z : Scheme.{u}, QuasiIso (augmentation Λ S Z) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
        (.up ℤ)).obj (complex Λ S Z)) ∧
    ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C)) ∧
  ∃ β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z,
    (∀ Z, AugmentationNormalized a S t Z (β Z)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
        (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj K) ≫
        (restriction a X).map ((D.theta a f).inv.app K) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj K)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
        (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
      (β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
        (restriction a Y).map (gamma D a f K) ≫
        (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
        (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K) =
      projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
        (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
        (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
      IsIso (projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
        (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K) ∧
      IsIso (gamma D a f K))

/-- The integral finite scalar perfect model, with the point arrows specified by their
actual section formulas. The finite free coordinate module and its scalar action are
the existing continuousSectionsModule with its recorded pointwise scalar action.
Source: blueprint integral-to-finite bullet
(blueprint: lem-sfb-integral-finite-scalar-perfect-model). -/
def PerfectModel (O A : Type u) [CommRing O] [CommRing A]
    [TopologicalSpace O] [TopologicalSpace A] [IsTopologicalRing O] [IsTopologicalRing A]
    (a : O →+* A) (ha : Continuous a) (D : ScalarSixPullbackData.{u}) : Prop :=
  letI := a.toAlgebra
  letI := continuousSMul_of_algebraMap O A ha
  letI : HasFiniteBiproducts (PointModules (condensed O)) := .of_hasFiniteProducts
  ∃ (r : ℕ) (q : (Fin r → O) →L[O] A) (φ : (Fin r → O) →L[O] (Fin r → O)),
    Function.Surjective q ∧ Function.Injective φ ∧ Function.Exact φ q ∧
    (∃ M : Matrix (Fin r) (Fin r) O, ∀ x : Fin r → O, φ x = M.mulVec x) ∧
    Nonempty (Profinite.continuousSectionsModule O (Fin r → O) ≅
      biproduct (fun _i : Fin r ↦ Mod.regular (Profinite.continuousCoefficientRingObj O))) ∧
    (Subsingleton A → r = 0) ∧
    ∃ (F : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O (Fin r → O))
       (G : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O A)
       (h : F ≫ G = 0)
       (t : (ShortComplex.mk F G h).X₃ ≅
          (Mod.comap (condensedMap a ha).hom.hom).obj
            (Mod.regular (Profinite.continuousCoefficientRingObj A))),
      (∀ (S : Profinite.{u}) (v : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((F.hom.hom.app (op S)) v).down s = φ (v.down s)) ∧
      (∀ (S : Profinite.{u}) (v : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((G.hom.hom.app (op S)) v).down s = q (v.down s)) ∧
      t.hom.hom = 𝟙 (Profinite.continuousCoefficientRingObj A) ∧
      (ShortComplex.mk F G h).ShortExact ∧
      DerivedAssertions D (condensedMap a ha) (ShortComplex.mk F G h) t

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
