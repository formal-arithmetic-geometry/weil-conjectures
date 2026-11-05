/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarInverseImageTowerDiagram
public import WeilConjectures.AlgebraicGeometry.RingedScalarExtensionComplexAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarInverseImageTowerDiagram
import Mathlib.CategoryTheory.Preadditive.LeftExact
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRestrictionOrdinaryComparisons
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import all WeilConjectures.Algebra.Homology.SmoothPurity.BasedTensorEvaluation
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Predicate
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Unbounded derived finite-free scalar coordinates

Source: Stacks Project, Modules on Sites, Tag 03EL; blueprint main-20261015,
sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients,
sk-prop-sfb-cartesian-coefficients-finite-free.proof.md.
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u w uA vA uB vB uA' vA' uB' vB'
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory ChangeOfRings
open CategoryTheory.MonoidalCategory
namespace SheafOfModules.RingedTensor

attribute [local instance 100000] coordinateAbelianSheafify coordinateAbelianLocalEquivalences

attribute [local instance 100000] coordinateCommRingToTypeCompose
  coordinateAddCommGrpToTypeCompose

attribute [local instance 100000] coordinateFiniteProductShape

section DerivedCompatibilityDefinition
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

end DerivedCompatibilityDefinition

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : ℕ)

attribute [local instance 50000]
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Limits.limit CategoryTheory.Limits.colimit

@[irreducible] private noncomputable def ordinaryCoordinates
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) :
    tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim :=
  NatIso.ofComponents (SheafOfModules.scalarExtensionIso a d θ)
    (fun f ↦ SheafOfModules.scalarExtensionIso_naturality a d θ f)

attribute [local irreducible] tensorFunctor scalarBasisCoordinate scalarBasisInclusion
  DerivedCategory.Q

attribute [local irreducible] Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FinitePowers

section
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasFiniteProducts A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasFiniteProducts B]

@[irreducible] private noncomputable def powerComparison (F : A ⥤ B) [F.Additive] (n : ℕ) :
    (Functor.const (Discrete (Fin n)) ⋙ lim) ⋙ F ≅
      F ⋙ (Functor.const (Discrete (Fin n)) ⋙ lim) :=
  NatIso.ofComponents (fun M ↦ PreservesProduct.iso F (fun _ : Fin n ↦ M)) (by
    intro M N f
    apply limit.hom_ext
    rintro ⟨i⟩
    simp only [Category.assoc]
    change F.map (lim.map ((Functor.const (Discrete (Fin n))).map f)) ≫
        (piComparison F (fun _ : Fin n ↦ N)) ≫ Pi.π (fun _ : Fin n ↦ F.obj N) i =
      (piComparison F (fun _ : Fin n ↦ M)) ≫
        lim.map ((Functor.const (Discrete (Fin n))).map (F.map f)) ≫
          Pi.π (fun _ : Fin n ↦ F.obj N) i
    erw [piComparison_comp_π, limMap_π, ← F.map_comp, limMap_π,
      piComparison_comp_π_assoc]
    simp only [Functor.map_comp]
    rfl)

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A]

attribute [local irreducible] cochainPowerIso

attribute [local irreducible] cochainPowerNatIso

attribute [local irreducible] powerLocalization

end

end FinitePowers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section OrdinaryInverseImage

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
  (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
  {R' S' : Sheaf J' CommRingCat.{u}}
  (IR : AlgebraicInverseImage g.inverse R R')
  (IS : AlgebraicInverseImage g.inverse S S') (a' : R' ⟶ S')
  (ha : g.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map a) ≫
    IS.ringUnderlying.hom = IR.ringUnderlying.hom ≫
      (sheafCompose J' (CategoryTheory.forget CommRingCat)).map a')

attribute [local semireducible] tensorFunctor

attribute [local irreducible] tensorFunctor scalarPure

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end OrdinaryInverseImage

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[irreducible] private noncomputable def descendIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B]
    {F G : DerivedCategory A ⥤ B} (e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G) :
    F ≅ G :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) B).preimageIso e

section CoordinateDescent

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (T : A ⥤ B) [T.Additive] (U : B ⥤ A) [U.Additive] (d : ℕ)
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

@[irreducible] private noncomputable def coordinateDescent
    (E : DerivedCategory A ⥤
      DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶
      T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [IsIso ε]
    (φ : T ⋙ U ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) :
    E ⋙ U.mapDerivedCategory.{w, w} ≅
      Functor.const (Discrete (Fin d)) ⋙ lim :=
  descendIso (A := A) (
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso ε) U.mapDerivedCategory.{w, w} ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
      U.mapDerivedCategoryFactors.{w, w} ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ U))
        (.up ℤ) ≪≫ NatIso.mapHomologicalComplex φ (.up ℤ)) DerivedCategory.Q ≪≫
    powerLocalization (A := A) d)

section InverseImageDescent

variable {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  (F : A ⥤ A') (G : B ⥤ B') (T' : A' ⥤ B') [T'.Additive] (U' : B' ⥤ A') [U'.Additive]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (E : DerivedCategory A ⥤
    DerivedCategory B)
  (ε : DerivedCategory.Q ⋙ E ⟶
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [IsIso ε]
  (E' : DerivedCategory A' ⥤
    DerivedCategory B')
  (ε' : DerivedCategory.Q ⋙ E' ⟶
    T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [IsIso ε']
  (χ : T ⋙ G ≅ F ⋙ T')

@[irreducible] private noncomputable def scalarComparisonDescent :
    E ⋙ G.mapDerivedCategory.{w, w} ≅
      F.mapDerivedCategory.{w, w} ⋙ E' :=
  descendIso (A := A) (
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso ε) G.mapDerivedCategory.{w, w} ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
      G.mapDerivedCategoryFactors.{w, w} ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G))
        (.up ℤ) ≪≫ NatIso.mapHomologicalComplex χ (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T'))
          (.up ℤ)).symm) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) (asIso ε').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors.{w, w}.symm E' ≪≫
    Functor.associator _ _ _)

@[irreducible] private noncomputable def derivedRestrictionComparison
    [PreservesFiniteLimits (U')]
    [PreservesFiniteColimits (U')]
    (ρ : U ⋙ F ≅ G ⋙ U') :
    U.mapDerivedCategory.{w, w} ⋙
        F.mapDerivedCategory.{w, w} ≅
      G.mapDerivedCategory.{w, w} ⋙
        U'.mapDerivedCategory.{w, w} :=
  (Functor.mapDerivedCategoryCompIso (U) F).symm ≪≫
    Functor.mapDerivedCategoryNatIso ρ ≪≫
      Functor.mapDerivedCategoryCompIso G (U')

variable [PreservesFiniteLimits (U')]
  [PreservesFiniteColimits (U')]

end InverseImageDescent

end CoordinateDescent

attribute [local irreducible] FiniteFreeCoordinatePullbackLaws FiniteFreeCoordinatesInverseImage

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexCompIso
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

end SheafOfModules.RingedTensor
