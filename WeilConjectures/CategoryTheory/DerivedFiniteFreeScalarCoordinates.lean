/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarInverseImageTowerDiagram
public import WeilConjectures.AlgebraicGeometry.RingedScalarExtensionComplexAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.ScalarInverseImageTowerDiagram
import Mathlib.CategoryTheory.Preadditive.LeftExact
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.FlatRestrictionOrdinaryComparisons
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
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
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
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExactSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteFreeScalarExtension
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation
import WeilConjectures.AlgebraicGeometry.FinitePowerComplex
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

/-- Small-site abelian sheafification, using the existing instance. -/
theorem coordinateAbelianSheafify {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) : HasSheafify K AddCommGrpCat.{u} := inferInstance

/-- Small-site local equivalences, using the existing instance. -/
theorem coordinateAbelianLocalEquivalences {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance 100000] coordinateAbelianSheafify coordinateAbelianLocalEquivalences

/-- The existing forgetful composition from commutative rings to rings. -/
theorem coordinateCommRingToRingCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

/-- The existing forgetful composition from commutative rings to sets. -/
theorem coordinateCommRingToTypeCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.HasSheafCompose (CategoryTheory.forget CommRingCat.{u}) := inferInstance

/-- The existing forgetful composition from abelian groups to sets. -/
theorem coordinateAddCommGrpToTypeCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) := inferInstance

attribute [local instance 100000] coordinateCommRingToRingCompose coordinateCommRingToTypeCompose
  coordinateAddCommGrpToTypeCompose


/-- Finite products in a small-site module category, cached from the existing limits instance. -/
theorem coordinateFiniteProductShape {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (A : Sheaf K RingCat.{u}) (n : ℕ) :
    HasLimitsOfShape (Discrete (Fin n)) (SheafOfModules.{u} A) := inferInstance

attribute [local instance 100000] coordinateFiniteProductShape

/-- A tuple of the eight ordinary comparison maps.
Source: Stacks 03EL (blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
structure OrdinaryComparisonTuple (A B C D E F G H : Type*) where
  chi : A
  rho : B
  sigma : C
  unitR : D
  unitS : E
  powerUnit : F
  basis : G
  coordinate : H

section DerivedCompatibilityDefinition
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

/-- The three normalized derived comparisons associated to an ordinary coordinate square.
Source: Stacks 03EL, 06YY, 015F, localization of the ordinary square
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def DerivedCoordinateCompatibility
    (T : A ⥤ B) [T.Additive] (U : B ⥤ A) [U.Additive] (d : ℕ)
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : A ⥤ A') (G : B ⥤ B') (T' : A' ⥤ B') [T'.Additive]
    (U' : B' ⥤ A') [U'.Additive]
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (E : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (E' : DerivedCategory A' ⥤ DerivedCategory B')
    (ε' : DerivedCategory.Q ⋙ E' ⟶ T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (χ : T ⋙ G ≅ F ⋙ T') (ρ : U ⋙ F ≅ G ⋙ U')
    (Φ : E ⋙ U.mapDerivedCategory ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (Normalized : (E' ⋙ U'.mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) → Prop) : Prop :=
    ∃ (Φ' : E' ⋙ U'.mapDerivedCategory ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)
      (β : E ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ E')
      (σD : (Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ F.mapDerivedCategory ≅
        F.mapDerivedCategory ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim)),
      (∀ K : CochainComplex A' ℤ,
        IsIso (ε'.app K)) ∧
      Normalized Φ' ∧
      (∀ (K : DerivedCategory A) (i : Fin d),
        σD.hom.app K ≫ Pi.π (fun _ : Fin d ↦ F.mapDerivedCategory.obj K) i =
          F.mapDerivedCategory.map (Pi.π (fun _ : Fin d ↦ K) i)) ∧
      (∀ K : CochainComplex A ℤ,
        β.hom.app (DerivedCategory.Q.obj K) ≫
            E'.map (F.mapDerivedCategoryFactors.hom.app K) ≫
            ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
          G.mapDerivedCategory.map (ε.app K) ≫
            G.mapDerivedCategoryFactors.hom.app
              ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
                (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
                (Functor.mapHomologicalComplexCompIso
                  (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K)) ∧
      ∀ K : DerivedCategory A,
        F.mapDerivedCategory.map (Φ.hom.app K) ≫ σD.hom.app K =
          ((Functor.mapDerivedCategoryCompIso U F).symm ≪≫
            Functor.mapDerivedCategoryNatIso ρ ≪≫
            Functor.mapDerivedCategoryCompIso G U').hom.app
              (E.obj K) ≫
            U'.mapDerivedCategory.map (β.hom.app K) ≫
            Φ'.hom.app (F.mapDerivedCategory.obj K)

end DerivedCompatibilityDefinition

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : ℕ)

attribute [local instance 50000]
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

/-- The basis inclusion, with the finite product serving also as the finite direct sum.
Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def scalarBasisInclusion
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) (i : Fin d) :
    unit (ringSheaf R) ⟶ (restriction.{u, u} a).obj (unit (ringSheaf S)) :=
  Pi.lift (fun j : Fin d ↦ if i = j then 𝟙 _ else 0) ≫ θ.hom

/-- The inverse basis coordinate. Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def scalarBasisCoordinate
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) (i : Fin d) :
    (restriction.{u, u} a).obj (unit (ringSheaf S)) ⟶ unit (ringSheaf R) :=
  θ.inv ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two local formulas, expressed using sheafification images of elementary tensors.
Source: Stacks 03EL and the blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def IsFiniteFreeScalarCoordinateIso
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  (∀ (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) (i : Fin d),
    ((φ.hom.app M) ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app U
      (scalarPure a M U s m) =
        (scalarBasisCoordinate a d θ i).val.app U s • m) ∧
  ∀ (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (x : ((Functor.const (Discrete (Fin d)) ⋙ lim).obj M).val.obj U),
    (φ.inv.app M).val.app U x =
      ∑ i : Fin d, scalarPure a M U
        ((scalarBasisInclusion a d θ i).val.app U
          (@id ((unit (ringSheaf R)).val.obj U) (1 : R.obj.obj U)))
        ((Pi.π (fun _ : Fin d ↦ M) i).val.app U x)

/-- Counit-normalized coordinates on every unbounded cochain representative.
Source: Stacks 03EL and blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def IsDerivedFiniteFreeScalarCoordinateIso
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ (K : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ) (i : Fin d),
    Φ.hom.app (DerivedCategory.Q.obj K) ≫
      Pi.π (fun _ : Fin d ↦ DerivedCategory.Q.obj K) i =
    (restriction.{u, u} a).mapDerivedCategory.map (ε.app K) ≫
      (restriction.{u, u} a).mapDerivedCategoryFactors.hom.app
        (((tensorFunctor a).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((((Functor.mapHomologicalComplexCompIso (Iso.refl
          (tensorFunctor a ⋙ restriction.{u, u} a)) (.up ℤ)).hom.app K) ≫
          (φ.hom.mapHomologicalComplex (.up ℤ)).app K) ≫
          ((Functor.whiskerLeft (Functor.const (Discrete (Fin d)))
            (lim.π ⟨i⟩)).mapHomologicalComplex (.up ℤ)).app K)

/-- Exactness assumptions for the pullback coordinate frame.
Source: Stacks 03EL, exactness of finite powers
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
structure FiniteFreeCoordinatePullbackExactness
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S') (a' : R' ⟶ S') : Prop where
  irAdd : IR.modules.Additive
  irLim : PreservesFiniteLimits IR.modules
  irColim : PreservesFiniteColimits IR.modules
  isAdd : IS.modules.Additive
  isLim : PreservesFiniteLimits IS.modules
  isColim : PreservesFiniteColimits IS.modules
  tensorLim : PreservesFiniteLimits (tensorFunctor a')
  tensorColim : PreservesFiniteColimits (tensorFunctor a')
  resLim : PreservesFiniteLimits (restriction.{u, u} a')
  resColim : PreservesFiniteColimits (restriction.{u, u} a')
  powerAdd : (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive
  powerLim : PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))
  powerColim : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))

/-- Chosen ordinary inverse-image coordinate maps, with equations stated separately.
Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
abbrev FiniteFreeCoordinatePullbackData
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S') (a' : R' ⟶ S') :=
  OrdinaryComparisonTuple
    (tensorFunctor a ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor a')
    (restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
    ((Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ IR.modules ≅
        IR.modules ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim))
    (IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (IR.modules.obj (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R))) ≅
        ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')))
    (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')) ≅
        (restriction.{u, u} a').obj (unit (ringSheaf S')))
    (tensorFunctor a' ⋙ restriction.{u, u} a' ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)

/-- Normalization equations for a pullback coordinate frame, verbatim from
`FiniteFreeCoordinatesInverseImage`. Source: Stacks 03EL
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def FiniteFreeCoordinatePullbackLaws
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S')
    (a' : R' ⟶ S')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S'))]
    [IR.modules.Additive]
    [PreservesFiniteLimits IR.modules]
    [PreservesFiniteColimits IR.modules]
    [IS.modules.Additive]
    [PreservesFiniteLimits IS.modules]
    [PreservesFiniteColimits IS.modules]
    [PreservesFiniteLimits (tensorFunctor a')]
    [PreservesFiniteColimits (tensorFunctor a')]
    [PreservesFiniteLimits (restriction.{u, u} a')]
    [PreservesFiniteColimits (restriction.{u, u} a')]
    [(Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))]
    (D : FiniteFreeCoordinatePullbackData a d g R' S' IR IS a') : Prop :=
      IsScalarInverseImageComparison g.inverse IR IS a a' D.chi ∧
      (underlying R').map D.unitR.hom =
        IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom ∧
      (underlying S').map D.unitS.hom =
        IS.moduleUnderlying.hom.app (unit (ringSheaf S)) ≫ IS.ringUnderlying.hom ∧
      (∀ i : Fin d, D.powerUnit.hom ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R')) i =
        IR.modules.map (Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i) ≫ D.unitR.hom) ∧
      (D.powerUnit.hom ≫ D.basis.hom = IR.modules.map θ.hom ≫
        D.rho.hom.app (unit (ringSheaf S)) ≫ (restriction.{u, u} a').map D.unitS.hom) ∧
      IsFiniteFreeScalarCoordinateIso a' d D.basis D.coordinate ∧
      (∀ N : SheafOfModules.{u} (ringSheaf S),
        (underlying R').map (D.rho.hom.app N) ≫
          IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N)) ∧
      (∀ (M : SheafOfModules.{u} (ringSheaf R)) (i : Fin d),
        D.sigma.hom.app M ≫ Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i =
          IR.modules.map (Pi.π (fun _ : Fin d ↦ M) i)) ∧
      (∀ M : SheafOfModules.{u} (ringSheaf R),
        IR.modules.map (φ.hom.app M) ≫ D.sigma.hom.app M =
          D.rho.hom.app ((tensorFunctor a).obj M) ≫
            (restriction.{u, u} a').map (D.chi.hom.app M) ≫
              D.coordinate.hom.app (IR.modules.obj M)) ∧
      ∀ (E' : DerivedCategory (SheafOfModules.{u} (ringSheaf R')) ⥤
          DerivedCategory (SheafOfModules.{u} (ringSheaf S')))
        (ε' : DerivedCategory.Q ⋙ E' ⟶
          (tensorFunctor a').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        [E'.IsLeftDerivedFunctor ε'
          (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf R')) (.up ℤ))],
        DerivedCoordinateCompatibility (tensorFunctor a) (restriction a) d
          IR.modules IS.modules (tensorFunctor a') (restriction a') E ε E' ε'
          D.chi D.rho Φ (IsDerivedFiniteFreeScalarCoordinateIso a' d E' ε' D.coordinate)

/-- Inverse image respects the specified coordinate morphisms. Restriction is normalized
on underlying sheaves, finite sums by their projections, and scalar extension by the
balanced comparison on arbitrary generalized elements. Thus none of the comparisons
is an arbitrary isomorphism.
Source: Stacks 03EL and blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def FiniteFreeCoordinatesInverseImage
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S')
    (a' : R' ⟶ S')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S'))],
    g.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map a) ≫
      IS.ringUnderlying.hom = IR.ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat)).map a' →
    ∃ h : FiniteFreeCoordinatePullbackExactness d g R' S' IR IS a',
      letI := h.irAdd
      letI := h.irLim
      letI := h.irColim
      letI := h.isAdd
      letI := h.isLim
      letI := h.isColim
      letI := h.tensorLim
      letI := h.tensorColim
      letI := h.resLim
      letI := h.resColim
      letI := h.powerAdd
      letI := h.powerLim
      letI := h.powerColim
      ∃ (D : FiniteFreeCoordinatePullbackData a d g R' S' IR IS a'),
      FiniteFreeCoordinatePullbackLaws a d θ φ E ε Φ g R' S' IR IS a' D

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

private theorem ordinaryCoordinates_forward
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) (i : Fin d) :
    ((ordinaryCoordinates a d θ).hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app U
      (scalarPure a M U s m) = (scalarBasisCoordinate a d θ i).val.app U s • m := by
  unfold ordinaryCoordinates
  exact SheafOfModules.scalarExtensionIso_tmul a d θ M U s m i

private theorem coordinate_basis
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (U : Cᵒᵖ) (i j : Fin d) :
    (scalarBasisCoordinate a d θ j).val.app U
      ((scalarBasisInclusion a d θ i).val.app U
        (@id ((unit (ringSheaf R)).val.obj U) (1 : R.obj.obj U))) =
      if i = j then (1 : R.obj.obj U) else 0 := by
  classical
  have h : scalarBasisInclusion a d θ i ≫ scalarBasisCoordinate a d θ j =
      if i = j then 𝟙 _ else 0 := by
    simp [scalarBasisInclusion, scalarBasisCoordinate, Category.assoc]
  by_cases hij : i = j
  · rw [if_pos hij] at h ⊢
    have h' := congrArg (fun f ↦ f.val.app U
      (@id ((unit (ringSheaf R)).val.obj U) (1 : R.obj.obj U))) h
    exact h'
  · rw [if_neg hij] at h ⊢
    have h' := congrArg (fun f ↦ f.val.app U
      (@id ((unit (ringSheaf R)).val.obj U) (1 : R.obj.obj U))) h
    exact h'.trans (by
      change ((forget (ringSheaf R) ⋙ PresheafOfModules.evaluation _ U).map
        (0 : unit (ringSheaf R) ⟶ unit (ringSheaf R))) _ = _
      rw [Functor.map_zero]
      rfl)

private theorem sectionIso_injective
    {M N : SheafOfModules.{u} (ringSheaf R)} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Injective (e.hom.val.app U) := by
  intro x y h
  have hi (z : M.val.obj U) : e.inv.val.app U (e.hom.val.app U z) = z :=
    congrArg (fun f ↦ f.val.app U z) e.hom_inv_id
  exact (hi x).symm.trans ((congrArg (e.inv.val.app U) h).trans (hi y))

private theorem coordinateIso_normalized
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (hφ : ∀ (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
      (s : S.obj.obj U) (m : M.val.obj U) (i : Fin d),
      (φ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app U
        (scalarPure a M U s m) = (scalarBasisCoordinate a d θ i).val.app U s • m) :
    IsFiniteFreeScalarCoordinateIso a d θ φ := by
  classical
  unfold IsFiniteFreeScalarCoordinateIso
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      constructor
  · exact hφ
  intro M U x
  apply sectionIso_injective (φ.app M) U
  apply SheafOfModules.sectionProduct_ext d M U
  intro j
  change ((φ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).val.app U)
      ((φ.inv.app M).val.app U x) =
    ((φ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).val.app U) _
  rw [map_sum]
  simp only [hφ, coordinate_basis, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h := congrArg (fun f ↦ f.val.app U x) (φ.inv_hom_id_app M)
  have hi : (φ.hom.app M).val.app U
      ((φ.inv.app M).val.app U x) = x := h
  change (Pi.π (fun _ : Fin d ↦ M) j).val.app U
      ((φ.hom.app M).val.app U
        ((φ.inv.app M).val.app U x)) = _
  exact congrArg ((Pi.π (fun _ : Fin d ↦ M) j).val.app U) hi

private theorem ordinaryCoordinates_normalized
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) :
    IsFiniteFreeScalarCoordinateIso a d θ (ordinaryCoordinates a d θ) :=
  coordinateIso_normalized a d θ (ordinaryCoordinates a d θ)
    (ordinaryCoordinates_forward a d θ)

attribute [local irreducible] tensorFunctor scalarBasisCoordinate scalarBasisInclusion
  DerivedCategory.Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_exact :
    PreservesFiniteLimits (restriction.{u, u} a) ∧
      PreservesFiniteColimits (restriction.{u, u} a) := by
  exact ⟨SheafOfModules.restriction_limits a, SheafOfModules.restriction_colimits a⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem extension_exact
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) :
    PreservesFiniteLimits (tensorFunctor a) ∧
      PreservesFiniteColimits (tensorFunctor a) := by
  have : PreservesFiniteLimits (restriction.{u, u} a) := (restriction_exact a).1
  have : PreservesFiniteColimits (restriction.{u, u} a) := (restriction_exact a).2
  have : (restriction.{u, u} a ⋙ toSheaf (ringSheaf R)).ReflectsIsomorphisms :=
    inferInstanceAs (toSheaf (ringSheaf S)).ReflectsIsomorphisms
  have : (restriction.{u, u} a).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp (restriction.{u, u} a) (toSheaf (ringSheaf R))
  have : PreservesFiniteLimits (tensorFunctor a ⋙ restriction.{u, u} a) :=
    preservesFiniteLimits_of_natIso (ordinaryCoordinates a d θ).symm
  have : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)) :=
    (SheafOfModules.power_exact _ d).2
  have : PreservesFiniteColimits (tensorFunctor a ⋙ restriction.{u, u} a) :=
    preservesFiniteColimits_of_natIso (ordinaryCoordinates a d θ).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (restriction a),
    preservesFiniteColimits_of_reflects_of_preserves _ (restriction a)⟩

attribute [local irreducible] Functor.mapDerivedCategory


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedCounit_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (E : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [E.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))] : IsIso ε := by
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts E ε
    (W := HomologicalComplex.quasiIso A (.up ℤ))
  intro K L f hf
  have : QuasiIso f := hf
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

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

private theorem powerComparison_π (F : A ⥤ B) [F.Additive] (n : ℕ) (M : A)
    (i : Fin n) :
    (powerComparison F n).hom.app M ≫ Pi.π (fun _ : Fin n ↦ F.obj M) i =
      F.map (Pi.π (fun _ : Fin n ↦ M) i) := by
  unfold powerComparison
  exact piComparison_comp_π F _ i


private theorem powerComparison_π_assoc (F : A ⥤ B) [F.Additive] (n : ℕ) (M : A)
    (i : Fin n) {Z : B} (f : F.obj M ⟶ Z) :
    (powerComparison F n).hom.app M ≫ Pi.π (fun _ : Fin n ↦ F.obj M) i ≫ f =
      F.map (Pi.π (fun _ : Fin n ↦ M) i) ≫ f := by
  rw [← Category.assoc, powerComparison_π]

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A]

private noncomputable def cochainPowerIso (n : ℕ)
    (K : CochainComplex A ℤ) :
    (((Functor.const (Discrete (Fin n)) ⋙ lim).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ∏ᶜ (fun _ : Fin n ↦ K) :=
  (NatIso.mapHomologicalComplex (finitePowerFunctorIso n) (.up ℤ)).app K ≪≫
    finitePowerComplexIso n K

private theorem cochainPowerIso_projection (n : ℕ)
    (K : CochainComplex A ℤ) (i : Fin n) :
    (cochainPowerIso n K).hom ≫ Pi.π (fun _ : Fin n ↦ K) i =
      ((Functor.whiskerLeft (Functor.const (Discrete (Fin n)))
        (lim.π ⟨i⟩)).mapHomologicalComplex (.up ℤ)).app K := by
  ext k
  simp only [cochainPowerIso, Iso.trans_hom, Iso.app_hom, Category.assoc,
    HomologicalComplex.comp_f]
  rw [← HomologicalComplex.comp_f, finitePowerComplexIso_projection]
  change (finitePowerFunctorIso n).hom.app (K.X k) ≫
    Pi.π (fun _ : Fin n ↦ K.X k) i = _
  exact Pi.isoLimit_inv_π _ i

attribute [local irreducible] cochainPowerIso

private noncomputable def cochainPowerNatIso (n : ℕ) :
    (Functor.const (Discrete (Fin n)) ⋙
      (lim : (Discrete (Fin n) ⥤ A) ⥤ A)).mapHomologicalComplex (.up ℤ) ≅
    Functor.const (Discrete (Fin n)) ⋙ lim :=
  NatIso.ofComponents (cochainPowerIso n) (by
    intro K L f
    apply limit.hom_ext
    rintro ⟨i⟩
    simp only [Category.assoc]
    change _ ≫ (cochainPowerIso n L).hom ≫ Pi.π (fun _ : Fin n ↦ L) i =
      (cochainPowerIso n K).hom ≫
        lim.map ((Functor.const (Discrete (Fin n))).map f) ≫ Pi.π (fun _ : Fin n ↦ L) i
    erw [limMap_π]
    change _ ≫ (cochainPowerIso n L).hom ≫ Pi.π (fun _ : Fin n ↦ L) i =
      (cochainPowerIso n K).hom ≫ Pi.π (fun _ : Fin n ↦ K) i ≫ f
    rw [cochainPowerIso_projection,
      ← Category.assoc (cochainPowerIso n K).hom (Pi.π (fun _ : Fin n ↦ K) i) f,
      cochainPowerIso_projection]
    exact (((Functor.whiskerLeft (Functor.const (Discrete (Fin n)))
      (lim.π ⟨i⟩)).mapHomologicalComplex (.up ℤ)).naturality f))

attribute [local irreducible] cochainPowerNatIso

private noncomputable def powerLocalization [HasDerivedCategory.{w} A]
    (n : ℕ) :
    (Functor.const (Discrete (Fin n)) ⋙
      (lim : (Discrete (Fin n) ⥤ A) ⥤ A)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ (Functor.const (Discrete (Fin n)) ⋙ lim) :=
  Functor.isoWhiskerRight (cochainPowerNatIso n) DerivedCategory.Q ≪≫
    powerComparison DerivedCategory.Q n

private theorem powerLocalization_projection [HasDerivedCategory.{w} A]
    (n : ℕ) (K : CochainComplex A ℤ) (i : Fin n) :
    (powerLocalization (A := A) n).hom.app K ≫
        Pi.π (fun _ : Fin n ↦ DerivedCategory.Q.obj K) i =
      DerivedCategory.Q.map
        (((Functor.whiskerLeft (Functor.const (Discrete (Fin n)))
          (lim.π (Discrete.mk i) : (lim : (Discrete (Fin n) ⥤ A) ⥤ A) ⟶ _))
          |>.mapHomologicalComplex (.up ℤ)).app K) := by
  simp only [powerLocalization, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  erw [powerComparison_π, ← Functor.map_comp]
  unfold cochainPowerNatIso
  change DerivedCategory.Q.map ((cochainPowerIso n K).hom ≫ _) = _
  exact congrArg DerivedCategory.Q.map (cochainPowerIso_projection n K i)

attribute [local irreducible] powerLocalization

end

end FinitePowers

private theorem power_naturality {A : Type*} [Category A] [HasFiniteProducts A]
    (n : ℕ) (F : A ⥤ A) (e : F ≅ Functor.const (Discrete (Fin n)) ⋙ lim)
    {X Y : A} (f : X ⟶ Y) (i : Fin n) :
    e.hom.app X ≫ Pi.π (fun _ : Fin n ↦ X) i ≫ f =
      F.map f ≫ e.hom.app Y ≫ Pi.π (fun _ : Fin n ↦ Y) i := by
  have hp := limMap_π ((Functor.const (Discrete (Fin n))).map f) ⟨i⟩
  change (Functor.const (Discrete (Fin n)) ⋙ lim).map f ≫
    Pi.π (fun _ : Fin n ↦ Y) i = Pi.π (fun _ : Fin n ↦ X) i ≫ f at hp
  calc
    _ = e.hom.app X ≫ (Functor.const (Discrete (Fin n)) ⋙ lim).map f ≫
        Pi.π (fun _ : Fin n ↦ Y) i := congrArg (e.hom.app X ≫ ·) hp.symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun h ↦ h ≫ Pi.π (fun _ : Fin n ↦ Y) i) (e.hom.naturality f).symm

private theorem inverseComparison {A : Type*} [Category A] {X Y Z : A}
    (e : X ≅ Y) (f : Y ≅ Z) (h : X ≅ Z)
    (he : e.hom ≫ f.hom = h.hom) : f.inv ≫ e.inv = h.inv := by
  apply (cancel_mono h.hom).mp
  calc
    (f.inv ≫ e.inv) ≫ h.hom = (f.inv ≫ e.inv) ≫ (e.hom ≫ f.hom) := by rw [he]
    _ = 𝟙 _ := by simp
    _ = h.inv ≫ h.hom := h.inv_hom_id.symm

private theorem inverse_map_comparison
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} (e : X ≅ Y) (q : F.obj Y ≅ F.obj X)
    (h : F.map e.hom = q.inv) : F.map e.inv = q.hom := by
  apply (cancel_epi (F.map e.hom)).mp
  rw [← F.map_comp, e.hom_inv_id, F.map_id, h, q.inv_hom_id]

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

private theorem inverseImage_exact :
    PreservesFiniteLimits IR.modules ∧ PreservesFiniteColimits IR.modules := by
  let I := CategoryTheory.GeometricMorphism.inverseImageUniverses.{u, u, u, u, u} IR
  have h := ((CategoryTheory.GeometricMorphism.geometric_inverse_image_exact
    J J' g).2.2 R).2 R' I
  exact (exactFunctor_iff _).mp h.1

private theorem inverseImage_map_section
    {M N : SheafOfModules.{u} (ringSheaf R)} (c : M ⟶ N)
    (T : Sheaf J (Type u)) (z : T ⟶ (underlying R).obj M)
    (U : C'ᵒᵖ) (q : (g.inverse.obj T).obj.obj U) :
    (g.inverse.map (z ≫ (underlying R).map c) ≫
        IR.moduleUnderlying.inv.app N).hom.app U q =
      (IR.modules.map c).val.app U
        ((g.inverse.map z ≫ IR.moduleUnderlying.inv.app M).hom.app U q) := by
  rw [g.inverse.map_comp, Category.assoc]
  have h := IR.moduleUnderlying.inv.naturality c
  change g.inverse.map ((underlying R).map c) ≫ IR.moduleUnderlying.inv.app N =
    IR.moduleUnderlying.inv.app M ≫ (underlying R').map (IR.modules.map c) at h
  rw [h]
  rfl

include ha in
private theorem restrictionComparison_exists :
    ∃ ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a',
      ∀ N : SheafOfModules.{u} (ringSheaf S),
        (underlying R').map (ρ.hom.app N) ≫ IS.moduleUnderlying.hom.app N =
          IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N) := by
  let : PreservesFiniteLimits g.inverse := g.leftExact
  have hc : IR.ringUnderlying.hom ≫
      (sheafCompose J' (CategoryTheory.forget CommRingCat)).map a' =
      g.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map a) ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((sheafCompose J (CategoryTheory.forget CommRingCat)).obj S))
          (rfl : g.inverse = g.inverse)) ≫ IS.ringUnderlying.hom := by
    simpa using ha.symm
  have hex (M : SheafOfModules.{u} (ringSheaf S)) :=
    CategoryTheory.FlatRingedDiagramInput.inverse_change_hom IR IS a a' rfl hc M
  let f (M : SheafOfModules.{u} (ringSheaf S)) := (hex M).choose
  have hf (M : SheafOfModules.{u} (ringSheaf S)) :
      (underlying R').map (f M) =
        IR.moduleUnderlying.hom.app ((restriction a).obj M) ≫
          IS.moduleUnderlying.inv.app M := by simpa using (hex M).choose_spec
  have hi (M : SheafOfModules.{u} (ringSheaf S)) : IsIso (f M) := by
    have : IsIso ((underlying R').map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso _ (underlying R')
  let ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a' :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (by
      intro M N h
      apply (underlying R').map_injective
      simp only [Functor.map_comp, asIso_hom, hf, Category.assoc]
      change (underlying R').map (IR.modules.map ((restriction a).map h)) ≫
          IR.moduleUnderlying.hom.app ((restriction a).obj N) ≫
            IS.moduleUnderlying.inv.app N =
        IR.moduleUnderlying.hom.app ((restriction a).obj M) ≫
          IS.moduleUnderlying.inv.app M ≫ (underlying S').map (IS.modules.map h)
      calc
        _ = IR.moduleUnderlying.hom.app ((restriction a).obj M) ≫
            g.inverse.map ((underlying R).map ((restriction a).map h)) ≫
              IS.moduleUnderlying.inv.app N :=
          IR.moduleUnderlying.hom.naturality_assoc ((restriction a).map h) _
        _ = _ := by
          apply congrArg (IR.moduleUnderlying.hom.app ((restriction a).obj M) ≫ ·)
          exact IS.moduleUnderlying.inv.naturality h)
  have hcomp (M : SheafOfModules.{u} (ringSheaf S)) :
      (underlying R').map (f M) ≫ IS.moduleUnderlying.hom.app M =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj M) := by
    rw [hf, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  exact ⟨ρ, hcomp⟩

include ha in
private theorem scalarComparison_exists :
    ∃ χ : tensorFunctor a ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor a',
      IsScalarInverseImageComparison g.inverse IR IS a a' χ := by
  let : PreservesFiniteLimits g.inverse := g.leftExact
  exact exists_scalarComparison g.inverse g.direct g.adj IR IS a a' ha

private theorem unitComparison_exists :
    ∃ κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'),
      (underlying R').map κ.hom =
        IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom := by
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_unit_iso R R' g.inverse IR
  have h : (underlying R').map e.inv =
      IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom :=
    inverse_map_comparison (underlying R') e
      (IR.moduleUnderlying.app (unit (ringSheaf R)) ≪≫ IR.ringUnderlying) he
  exact ⟨e.symm, h⟩

private noncomputable def transportedPower
    [IR.modules.Additive]
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R')) :
    IR.modules.obj (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R))) ≅
      ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')) :=
  PreservesProduct.iso IR.modules (fun _ : Fin d ↦ unit (ringSheaf R)) ≪≫
    Pi.mapIso (fun _ : Fin d ↦ κ)

private theorem transportedPower_projection
    [IR.modules.Additive]
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R')) (i : Fin d) :
    (transportedPower d g IR κ).hom ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R')) i =
      IR.modules.map (Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i) ≫ κ.hom := by
  simp [transportedPower, Category.assoc]

private noncomputable def transportedBasis
    [IR.modules.Additive]
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a') :
    ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')) ≅
      (restriction.{u, u} a').obj (unit (ringSheaf S')) :=
  (transportedPower d g IR κ).symm ≪≫ IR.modules.mapIso θ ≪≫
    ρ.app (unit (ringSheaf S)) ≪≫ (restriction a').mapIso κS

private theorem transportedBasis_hom
    [IR.modules.Additive]
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a') :
    (transportedPower d g IR κ).hom ≫
        (transportedBasis a d g IR IS a' θ κ κS ρ).hom =
      IR.modules.map θ.hom ≫ ρ.hom.app (unit (ringSheaf S)) ≫
        (restriction a').map κS.hom := by
  simp only [transportedBasis, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.hom_inv_id_assoc]

private theorem transportedBasis_coordinate
    [IR.modules.Additive]
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
    (i : Fin d) :
    ρ.hom.app (unit (ringSheaf S)) ≫ (restriction a').map κS.hom ≫
        scalarBasisCoordinate a' d (transportedBasis a d g IR IS a' θ κ κS ρ) i =
      IR.modules.map (scalarBasisCoordinate a d θ i) ≫ κ.hom := by
  simp only [scalarBasisCoordinate, transportedBasis, Iso.trans_inv, Iso.symm_inv,
    Iso.app_inv, Functor.mapIso_inv, Category.assoc]
  rw [← (restriction a').map_comp_assoc, κS.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [transportedPower_projection, Functor.map_comp]
  simp only [Category.assoc]

private theorem transportedCoordinate_underlying
    [IR.modules.Additive]
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
    (hκ : (underlying R').map κ.hom =
      IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom)
    (hκS : (underlying S').map κS.hom =
      IS.moduleUnderlying.hom.app (unit (ringSheaf S)) ≫ IS.ringUnderlying.hom)
    (hρ : ∀ N, (underlying R').map (ρ.hom.app N) ≫
      IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N))
    (i : Fin d) :
    g.inverse.map ((underlying R).map (scalarBasisCoordinate a d θ i)) ≫
        IR.ringUnderlying.hom =
      IS.ringUnderlying.hom ≫ (underlying R').map
        (scalarBasisCoordinate a' d (transportedBasis a d g IR IS a' θ κ κS ρ) i) := by
  have h := congrArg (underlying R').map
    (transportedBasis_coordinate a d g IR IS a' θ κ κS ρ i)
  simp only [Functor.map_comp] at h
  change (underlying R').map (ρ.hom.app (unit (ringSheaf S))) ≫
      (underlying S').map κS.hom ≫ _ = _ at h
  rw [hκS, hκ] at h
  simp only [← Category.assoc] at h
  rw [hρ] at h
  simp only [Category.assoc] at h
  have hn := IR.moduleUnderlying.hom.naturality_assoc (scalarBasisCoordinate a d θ i)
    IR.ringUnderlying.hom
  have hh := hn.symm.trans h.symm
  exact (cancel_epi (IR.moduleUnderlying.hom.app
    ((restriction a).obj (unit (ringSheaf S))))).mp hh

attribute [local irreducible] transportedPower transportedBasis

attribute [local semireducible] tensorFunctor

private theorem scalarPure_hom_ext
    (M N : SheafOfModules.{u} (ringSheaf R))
    (f h : (restriction.{u, u} a).obj ((tensorFunctor a).obj M) ⟶ N)
    (he : ∀ U s m, f.val.app U (scalarPure a M U s m) =
      h.val.app U (scalarPure a M U s m)) : f = h := by
  unfold tensorFunctor at f h
  apply SheafOfModules.scalarExtension_hom_ext a M N
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => exact he U s m
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private noncomputable def pureGraph
    (M : SheafOfModules.{u} (ringSheaf R)) :
    (sheafCompose J (CategoryTheory.forget CommRingCat)).obj S ⊗
      (underlying R).obj M ⟶ (underlying S).obj ((tensorFunctor a).obj M) :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ scalarPure a M U x.1 x.2)
     naturality := by
       intro U V f
       ext x
       change scalarPure a M V (S.obj.map f x.1) (M.val.map f x.2) =
         (((tensorFunctor a).obj M).val.map f) (scalarPure a M U x.1 x.2)
       unfold scalarPure
       have h := PresheafOfModules.naturality_apply
         ((PresheafOfModules.sheafificationAdjunction.{u}
           (𝟙 (ringSheaf S).obj)).unit.app (changeOfRingsPresheaf.{u, u, u} a M))
         f (x.1 ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x.2)
       dsimp only [Functor.id_obj] at h
       erw [SheafOfModules.tensorRestriction_tmul] at h
       exact h }⟩

attribute [local irreducible] tensorFunctor scalarPure

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem inverseImage_coordinate_square
    [IR.modules.Additive]
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
    (hκ : (underlying R').map κ.hom =
      IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom)
    (hκS : (underlying S').map κS.hom =
      IS.moduleUnderlying.hom.app (unit (ringSheaf S)) ≫ IS.ringUnderlying.hom)
    (hρ : ∀ N, (underlying R').map (ρ.hom.app N) ≫
      IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N))
    (χ : tensorFunctor a ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor a')
    (hχ : IsScalarInverseImageComparison g.inverse IR IS a a' χ)
    (M : SheafOfModules.{u} (ringSheaf R)) :
    IR.modules.map ((ordinaryCoordinates a d θ).hom.app M) ≫
        (powerComparison IR.modules d).hom.app M =
      ρ.hom.app ((tensorFunctor a).obj M) ≫ (restriction a').map (χ.hom.app M) ≫
        (ordinaryCoordinates a' d (transportedBasis a d g IR IS a' θ κ κS ρ)).hom.app
          (IR.modules.obj M) := by
  let : PreservesFiniteLimits g.inverse := g.leftExact
  let θ' := transportedBasis a d g IR IS a' θ κ κS ρ
  let φ := ordinaryCoordinates a d θ
  let φ' := ordinaryCoordinates a' d θ'
  let e : (restriction a ⋙ IR.modules).obj ((tensorFunctor a).obj M) ≅
      (restriction a').obj ((tensorFunctor a').obj (IR.modules.obj M)) :=
    ρ.app ((tensorFunctor a).obj M) ≪≫ (restriction a').mapIso (χ.app M)
  apply (cancel_epi e.inv).mp
  change e.inv ≫ _ = e.inv ≫ e.hom ≫ φ'.hom.app (IR.modules.obj M)
  rw [e.inv_hom_id_assoc]
  apply scalarPure_hom_ext a' (IR.modules.obj M)
  intro U s m
  apply SheafOfModules.sectionProduct_ext d (IR.modules.obj M) U
  intro i
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat)).obj S
  let Y := (underlying R).obj M
  let T := X ⊗ Y
  let q := FlatRingedDiagramInput.pairPreimage g.inverse X Y U
    (IS.ringUnderlying.inv.hom.app U s) ((IR.moduleUnderlying.hom.app M).hom.app U m)
  let x := (g.inverse.map (pureGraph a M) ≫
    IS.moduleUnderlying.inv.app ((tensorFunctor a).obj M)).hom.app U q
  have hs : (g.inverse.map (CartesianMonoidalCategory.fst X Y) ≫
      IS.ringUnderlying.hom).hom.app U q = s := by
    change IS.ringUnderlying.hom.hom.app U
      ((g.inverse.map (CartesianMonoidalCategory.fst X Y)).hom.app U q) = s
    erw [FlatRingedDiagramInput.pairPreimage_fst]
    exact congrArg (fun f ↦ f.hom.app U s) IS.ringUnderlying.inv_hom_id
  have hm : (g.inverse.map (CartesianMonoidalCategory.snd X Y) ≫
      IR.moduleUnderlying.inv.app M).hom.app U q = m := by
    change (IR.moduleUnderlying.inv.app M).hom.app U
      ((g.inverse.map (CartesianMonoidalCategory.snd X Y)).hom.app U q) = m
    erw [FlatRingedDiagramInput.pairPreimage_snd]
    exact congrArg (fun f ↦ f.hom.app U m) (IR.moduleUnderlying.hom_inv_id_app M)
  have hχx : (χ.hom.app M).val.app U x = scalarPure a' (IR.modules.obj M) U s m := by
    have h := hχ M T (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y) (pureGraph a M) (fun _ _ ↦ rfl) U q
    rw [hs, hm] at h
    exact h
  have hρinv : IS.moduleUnderlying.inv.app ((tensorFunctor a).obj M) ≫
      (underlying R').map (ρ.inv.app ((tensorFunctor a).obj M)) =
        IR.moduleUnderlying.inv.app ((restriction a).obj ((tensorFunctor a).obj M)) := by
    exact inverseComparison ((underlying R').mapIso
      (ρ.app ((tensorFunctor a).obj M)))
      (IS.moduleUnderlying.app ((tensorFunctor a).obj M))
      (IR.moduleUnderlying.app ((restriction a).obj ((tensorFunctor a).obj M)))
      (hρ ((tensorFunctor a).obj M))
  let c := φ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i
  let z : T ⟶ (underlying R).obj M := pureGraph a M ≫ (underlying R).map c
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have hz : ∀ V t, z.hom.app V t =
          (@id (R.obj.obj V) ((scalarBasisCoordinate a d θ i).val.app V t.1)) •
            (@id (M.val.obj V) t.2) := by
        intro V t
        exact ordinaryCoordinates_forward a d θ M V t.1 t.2 i
  have hmul := IR.moduleSMul M T
    (CartesianMonoidalCategory.fst X Y ≫
      (underlying R).map (scalarBasisCoordinate a d θ i))
    (CartesianMonoidalCategory.snd X Y) z hz U q
  have hc := transportedCoordinate_underlying a d g IR IS a' θ κ κS ρ hκ hκS hρ i
  have hr : (g.inverse.map (CartesianMonoidalCategory.fst X Y ≫
      (underlying R).map (scalarBasisCoordinate a d θ i)) ≫
      IR.ringUnderlying.hom).hom.app U q =
        (scalarBasisCoordinate a' d θ' i).val.app U s := by
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [g.inverse.map_comp, Category.assoc, hc]
    exact congrArg (fun x ↦ (scalarBasisCoordinate a' d θ' i).val.app U x) hs
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      change (g.inverse.map z ≫ IR.moduleUnderlying.inv.app M).hom.app U q =
        (@id (R'.obj.obj U) ((g.inverse.map
          (CartesianMonoidalCategory.fst X Y ≫
            (underlying R).map (scalarBasisCoordinate a d θ i)) ≫
          IR.ringUnderlying.hom).hom.app U q)) •
        (@id ((IR.modules.obj M).val.obj U) ((g.inverse.map
          (CartesianMonoidalCategory.snd X Y) ≫ IR.moduleUnderlying.inv.app M).hom.app U q))
        at hmul
  rw [hr, hm] at hmul
  have hn : (g.inverse.map z ≫ IR.moduleUnderlying.inv.app M).hom.app U q =
      (IR.modules.map c).val.app U
        ((g.inverse.map (pureGraph a M) ≫
          IR.moduleUnderlying.inv.app
            ((restriction a).obj ((tensorFunctor a).obj M))).hom.app U q) := by
    exact inverseImage_map_section g IR c T (pureGraph a M) U q
  have hx : (e.inv).val.app U (scalarPure a' (IR.modules.obj M) U s m) =
      (g.inverse.map (pureGraph a M) ≫
        IR.moduleUnderlying.inv.app
          ((restriction a).obj ((tensorFunctor a).obj M))).hom.app U q := by
    apply Eq.trans (congrArg (fun t ↦ e.inv.val.app U t) hχx.symm)
    dsimp only [e, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv]
    change (ρ.inv.app ((tensorFunctor a).obj M)).val.app U
      ((χ.inv.app M).val.app U ((χ.hom.app M).val.app U x)) = _
    have hi := congrArg (fun f ↦ f.val.app U x) (χ.hom_inv_id_app M)
    change (χ.inv.app M).val.app U ((χ.hom.app M).val.app U x) = x at hi
    rw [hi]
    exact congrArg (fun f ↦ (g.inverse.map (pureGraph a M) ≫ f).hom.app U q) hρinv
  change (Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i).val.app U
      (((IR.modules.map (φ.hom.app M) ≫ (powerComparison IR.modules d).hom.app M).val.app U)
        (e.inv.val.app U (scalarPure a' (IR.modules.obj M) U s m))) = _
  refine (congrArg (fun t ↦ (Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i).val.app U
    ((IR.modules.map (φ.hom.app M) ≫ (powerComparison IR.modules d).hom.app M).val.app U t))
      hx).trans ?_
  have hp : (powerComparison IR.modules d).hom.app M ≫
      Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i =
      IR.modules.map (Pi.π (fun _ : Fin d ↦ M) i) := by
    exact powerComparison_π _ _ _ i
  have hleft := congrArg (fun f ↦ f.val.app U
    ((g.inverse.map (pureGraph a M) ≫
      IR.moduleUnderlying.inv.app ((restriction a).obj ((tensorFunctor a).obj M))).hom.app U q))
    (show IR.modules.map (φ.hom.app M) ≫
        (powerComparison IR.modules d).hom.app M ≫
        Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i = IR.modules.map c by
      exact (congrArg (IR.modules.map (φ.hom.app M) ≫ ·) hp).trans
        (IR.modules.map_comp (φ.hom.app M) (Pi.π (fun _ : Fin d ↦ M) i)).symm)
  exact hleft.trans (hn.symm.trans
    (hmul.trans (ordinaryCoordinates_forward a' d θ' (IR.modules.obj M) U s m i).symm))

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

private theorem descendIso_app
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B]
    {F G : DerivedCategory A ⥤ B} (e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G)
    (K : CochainComplex A ℤ) :
    (descendIso e).hom.app (DerivedCategory.Q.obj K) = e.hom.app K := by
  unfold descendIso
  exact congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) B).map_preimage e.hom) K

section CoordinateDescent

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (T : A ⥤ B) [T.Additive] (U : B ⥤ A) [U.Additive] (d : ℕ)
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private def coordinateProjection
    (φ : T ⋙ U ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (K : CochainComplex A ℤ) (i : Fin d) :
    (U.mapHomologicalComplex (.up ℤ)).obj
      ((T.mapHomologicalComplex (.up ℤ)).obj K) ⟶ K :=
  ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ U)) (.up ℤ)).hom.app K ≫
    (φ.hom.mapHomologicalComplex (.up ℤ)).app K) ≫
      ((Functor.whiskerLeft (Functor.const (Discrete (Fin d)))
        (lim.π ⟨i⟩)).mapHomologicalComplex (.up ℤ)).app K

private def CoordinateNormalization
    (E : DerivedCategory A ⥤
      DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶
      T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φ : T ⋙ U ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ : E ⋙ U.mapDerivedCategory.{w, w} ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ (K : CochainComplex A ℤ) (i : Fin d),
    Φ.hom.app (DerivedCategory.Q.obj K) ≫
      Pi.π (fun _ : Fin d ↦ DerivedCategory.Q.obj K) i =
    U.mapDerivedCategory.map (ε.app K) ≫
      U.mapDerivedCategoryFactors.{w, w}.hom.app
        ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map (coordinateProjection T U d φ K i)

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

private theorem coordinateDescent_normalized
    (E : DerivedCategory A ⥤
      DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶
      T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [IsIso ε]
    (φ : T ⋙ U ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) :
    CoordinateNormalization T U d E ε φ (coordinateDescent T U d E ε φ) := by
  intro K i
  unfold coordinateProjection
  unfold coordinateDescent
  rw [descendIso_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  simp only [Functor.map_comp, NatIso.mapHomologicalComplex, Category.assoc]
  erw [powerLocalization_projection]

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

private theorem scalarNormalization {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y : A} (t : X ≅ Y) {Z W V U : B} (e : Z ≅ F.obj Y)
    (f : W ⟶ V) (g : V ⟶ U) (h : U ⟶ Z) :
    f ≫ g ≫ h ≫ e.hom ≫ F.map t.inv ≫ F.map t.hom ≫ e.inv = f ≫ g ≫ h := by
  rw [← F.map_comp_assoc, t.inv_hom_id, F.map_id, Category.id_comp,
    Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarComparisonDescent_normalized
    (K : CochainComplex A ℤ) :
    (scalarComparisonDescent T F G T' E ε E' ε' χ).hom.app
        (DerivedCategory.Q.obj K) ≫
        E'.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (ε.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
              (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
            (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso
              (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K) := by
  unfold scalarComparisonDescent
  rw [descendIso_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, asIso_hom, asIso_inv]
  simp only [NatIso.mapHomologicalComplex, Functor.comp_obj]
  exact scalarNormalization E' (F.mapDerivedCategoryFactors.app K)
    ((asIso ε').app ((F.mapHomologicalComplex (.up ℤ)).obj K)).symm _ _ _

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

private theorem derivedRestrictionComparison_spec
    [PreservesFiniteLimits (U')]
    [PreservesFiniteColimits (U')]
    (ρ : U ⋙ F ≅ G ⋙ U')
    (K : CochainComplex B ℤ) :
    (derivedRestrictionComparison U F G U' ρ).hom.app (DerivedCategory.Q.obj K) ≫
      U'.mapDerivedCategory.map
        (G.mapDerivedCategoryFactors.hom.app K) ≫
      U'.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategory.map
        (U.mapDerivedCategoryFactors.hom.app K) ≫
      F.mapDerivedCategoryFactors.hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((ρ.hom.mapHomologicalComplex (.up ℤ)).app K) := by
  unfold derivedRestrictionComparison
  exact Functor.exactSquare_fac ρ K

variable [PreservesFiniteLimits (U')]
  [PreservesFiniteColimits (U')]

private theorem derivedCoordinateSquare
    (ρ : U ⋙ F ≅ G ⋙ U')
    (φ : T ⋙ U ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (φ' : T' ⋙ U' ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (hφ : ∀ M, F.map (φ.hom.app M) ≫
        (powerComparison F d).hom.app M =
      ρ.hom.app (T.obj M) ≫
        U'.map (χ.hom.app M) ≫ φ'.hom.app (F.obj M))
    (Φ : E ⋙ U.mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ' : E' ⋙ U'.mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (hΦ : CoordinateNormalization T U d E ε φ Φ)
    (hΦ' : CoordinateNormalization T' U' d E' ε' φ' Φ')
    (K : DerivedCategory A) :
    F.mapDerivedCategory.map (Φ.hom.app K) ≫
        (powerComparison F.mapDerivedCategory d).hom.app K =
      ((Functor.mapDerivedCategoryCompIso U F).symm ≪≫
        Functor.mapDerivedCategoryNatIso ρ ≪≫
        Functor.mapDerivedCategoryCompIso G U').hom.app (E.obj K) ≫
        U'.mapDerivedCategory.map
          ((scalarComparisonDescent T F G T' E ε E' ε' χ).hom.app K) ≫
        Φ'.hom.app (F.mapDerivedCategory.obj K) := by
  let β := scalarComparisonDescent T F G T' E ε E' ε' χ
  let σD := powerComparison F.mapDerivedCategory d
  let ρD := derivedRestrictionComparison U F G U' ρ
  let lhs : (E ⋙ U.mapDerivedCategory) ⋙
      F.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙
        (Functor.const (Discrete (Fin d)) ⋙ lim) :=
    Functor.whiskerRight Φ.hom F.mapDerivedCategory ≫ σD.hom
  let rhs : (E ⋙ U.mapDerivedCategory) ⋙
      F.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙
        (Functor.const (Discrete (Fin d)) ⋙ lim) :=
    Functor.whiskerLeft E ρD.hom ≫
      Functor.whiskerRight β.hom U'.mapDerivedCategory ≫
      Functor.whiskerLeft F.mapDerivedCategory Φ'.hom
  suffices lhs = rhs by
    simpa only [lhs, rhs, β, σD, ρD, derivedRestrictionComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app] using congr_app this K
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (A) (.up ℤ))
  intro L
  apply limit.hom_ext
  rintro ⟨i⟩
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app L)).mp
  dsimp only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [Category.assoc]
  change F.mapDerivedCategory.map (Φ.hom.app (DerivedCategory.Q.obj L)) ≫
      σD.hom.app (DerivedCategory.Q.obj L) ≫ Pi.π (fun _ : Fin d ↦
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) i ≫
        F.mapDerivedCategoryFactors.hom.app L =
    ρD.hom.app (E.obj (DerivedCategory.Q.obj L)) ≫
      U'.mapDerivedCategory.map (β.hom.app (DerivedCategory.Q.obj L)) ≫
      Φ'.hom.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
      Pi.π (fun _ : Fin d ↦
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) i ≫
        F.mapDerivedCategoryFactors.hom.app L
  have hp : Φ'.hom.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
      Pi.π (fun _ : Fin d ↦
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) i ≫
        F.mapDerivedCategoryFactors.hom.app L =
    U'.mapDerivedCategory.map
        (E'.map (F.mapDerivedCategoryFactors.hom.app L)) ≫
      Φ'.hom.app (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        Pi.π (fun _ : Fin d ↦ DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj L)) i := by
    exact power_naturality d (E' ⋙ U'.mapDerivedCategory)
      Φ' (F.mapDerivedCategoryFactors.hom.app L) i
  dsimp only [σD]
  erw [powerComparison_π_assoc, ← F.mapDerivedCategory.map_comp_assoc, hΦ,
    hp, hΦ']
  simp only [Functor.map_comp, Category.assoc]
  erw [← U'.mapDerivedCategory.map_comp_assoc]
  erw [← U'.mapDerivedCategory.map_comp_assoc]
  dsimp only [β]
  simp only [Category.assoc]
  erw [scalarComparisonDescent_normalized]
  simp only [U'.mapDerivedCategory.map_comp, Category.assoc]
  erw [← ρD.hom.naturality_assoc (ε.app L)]
  erw [U'.mapDerivedCategoryFactors_hom_naturality_assoc]
  dsimp only [ρD]
  erw [reassoc_of% (derivedRestrictionComparison_spec U F G U' ρ
    ((T.mapHomologicalComplex (.up ℤ)).obj L))]
  simp only [Functor.comp_map]
  apply congrArg (F.mapDerivedCategory.map (U.mapDerivedCategory.map (ε.app L)) ≫ ·)
  erw [F.mapDerivedCategoryFactors_hom_naturality]
  simp only [← DerivedCategory.Q.map_comp]
  apply congrArg (F.mapDerivedCategory.map
    (U.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj L)) ≫ ·)
  apply congrArg (F.mapDerivedCategoryFactors.hom.app
    ((U.mapHomologicalComplex (.up ℤ)).obj
      ((T.mapHomologicalComplex (.up ℤ)).obj L)) ≫ ·)
  apply congrArg DerivedCategory.Q.map
  ext n
  have ht := congrArg (fun f ↦ f ≫ Pi.π (fun _ : Fin d ↦ F.obj (L.X n)) i)
    (hφ (L.X n))
  simp only [coordinateProjection, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.whiskerLeft_app, lim.π_app,
    Functor.mapHomologicalComplex_obj_X, Category.assoc]
  change F.map (𝟙 _ ≫ φ.hom.app (L.X n) ≫ Pi.π (fun _ : Fin d ↦ L.X n) i) =
    ρ.hom.app (T.obj (L.X n)) ≫
      U'.map (𝟙 _ ≫ χ.hom.app (L.X n) ≫ 𝟙 _) ≫
        (𝟙 _ ≫ φ'.hom.app (F.obj (L.X n)) ≫ Pi.π (fun _ : Fin d ↦ F.obj (L.X n)) i)
  simpa only [Category.id_comp, Category.comp_id, Functor.map_comp,
    powerComparison_π, Category.assoc] using ht

private theorem derivedCoordinateBundle
    (ρ : U ⋙ F ≅ G ⋙ U')
    (φ : T ⋙ U ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (φ' : T' ⋙ U' ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (hφ : ∀ M, F.map (φ.hom.app M) ≫ (powerComparison F d).hom.app M =
      ρ.hom.app (T.obj M) ≫ U'.map (χ.hom.app M) ≫ φ'.hom.app (F.obj M))
    (Φ : E ⋙ U.mapDerivedCategory ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (hΦ : CoordinateNormalization T U d E ε φ Φ)
    (Normalized : (E' ⋙ U'.mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) → Prop)
    (hNormalized : ∀ Ψ, CoordinateNormalization T' U' d E' ε' φ' Ψ → Normalized Ψ) :
    DerivedCoordinateCompatibility T U d F G T' U' E ε E' ε' χ ρ Φ Normalized := by
  refine ⟨coordinateDescent T' U' d E' ε' φ',
    scalarComparisonDescent T F G T' E ε E' ε' χ,
    powerComparison F.mapDerivedCategory d,
    (fun _ ↦ inferInstance),
    hNormalized _ (coordinateDescent_normalized T' U' d E' ε' φ'),
    (fun K i ↦ powerComparison_π _ _ _ i),
    scalarComparisonDescent_normalized T F G T' E ε E' ε' χ, ?_⟩
  exact derivedCoordinateSquare T U d F G T' U' E ε E' ε' χ ρ φ φ' hφ
    Φ _ hΦ (coordinateDescent_normalized T' U' d E' ε' φ')

end InverseImageDescent

end CoordinateDescent



attribute [local irreducible] transportedPower transportedBasis
  FiniteFreeCoordinatePullbackLaws FiniteFreeCoordinatesInverseImage

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexCompIso
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

private theorem normalization_specialization
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (h : CoordinateNormalization (tensorFunctor a) (restriction a) d E ε φ Φ) :
    IsDerivedFiniteFreeScalarCoordinateIso a d E ε φ Φ := by
  intro K i
  exact h K i

private theorem coordinates_inverseImage
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [IsIso ε]
    (hΦ : CoordinateNormalization (tensorFunctor a) (restriction a) d E ε
      (ordinaryCoordinates a d θ) Φ)
    :
    FiniteFreeCoordinatesInverseImage a d θ (ordinaryCoordinates a d θ) E ε Φ := by
  unfold FiniteFreeCoordinatesInverseImage
  intro C' _ J' g R' S' IR IS a' _ _ ha
  have : PreservesFiniteLimits g.inverse := g.leftExact
  have hIRlim := (inverseImage_exact g IR).1
  have hIRcolim := (inverseImage_exact g IR).2
  have hISlim := (inverseImage_exact g IS).1
  have hIScolim := (inverseImage_exact g IS).2
  have hIRadd : IR.modules.Additive := Functor.additive_of_preserves_binary_products _
  have hISadd : IS.modules.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨κ, hκ⟩ := unitComparison_exists g IR
  obtain ⟨κS, hκS⟩ := unitComparison_exists g IS
  obtain ⟨ρ, hρ⟩ := restrictionComparison_exists a g IR IS a' ha
  obtain ⟨χ, hχ⟩ := scalarComparison_exists a g IR IS a' ha
  let θ' := transportedBasis a d g IR IS a' θ κ κS ρ
  let φ' := ordinaryCoordinates a' d θ'
  have hBasis := transportedBasis_hom a d g IR IS a' θ κ κS ρ
  have hφ'Normalized := ordinaryCoordinates_normalized a' d θ'
  have hSquare := inverseImage_coordinate_square a d g IR IS a' θ κ κS ρ
    hκ hκS hρ χ hχ
  have hUlim := (restriction_exact a').1
  have hUcolim := (restriction_exact a').2
  have hTlim := (extension_exact a' d θ').1
  have hTcolim := (extension_exact a' d θ').2
  have hPadd : (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hPlim : PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)) := inferInstance
  have hPcolim : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)) :=
    (SheafOfModules.power_exact _ d).2
  let D : FiniteFreeCoordinatePullbackData a d g R' S' IR IS a' :=
    ⟨χ, ρ, powerComparison IR.modules d, κ, κS,
      transportedPower d g IR κ, θ', φ'⟩
  refine ⟨⟨hIRadd, hIRlim, hIRcolim, hISadd, hISlim, hIScolim,
    hTlim, hTcolim, hUlim, hUcolim, hPadd, hPlim, hPcolim⟩, D, ?_⟩
  unfold FiniteFreeCoordinatePullbackLaws
  dsimp only [D]
  refine ⟨hχ, hκ, hκS, transportedPower_projection d g IR κ, hBasis,
    hφ'Normalized, hρ, ?_, hSquare, ?_⟩
  · intro M i
    exact powerComparison_π _ _ _ i
  · intro E' ε' _
    have := derivedCounit_isIso (tensorFunctor a') E' ε'
    exact derivedCoordinateBundle (tensorFunctor a) (restriction a) d IR.modules IS.modules
      (tensorFunctor a') (restriction a') E ε E' ε' χ ρ
      (ordinaryCoordinates a d θ) φ'
      hSquare Φ hΦ
      (IsDerivedFiniteFreeScalarCoordinateIso a' d E' ε' φ')
      (normalization_specialization a' d E' ε' φ')


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Finite-free scalar extension is exact on all unbounded complexes. Its universal
left derived functor is computed termwise, with the specified coordinates; the
coordinate square commutes before localization and therefore after localization.
Source: Stacks 03EL, 06YY, 015F; blueprint main-20261015, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates).

Proof:
1. Reuse the natural finite-basis scalarExtensionIso. Its pure-tensor formula and
   the Kronecker-delta basis identities give both ordinary coordinate formulas.
2. Restriction preserves and reflects exactness through underlying abelian sheaves.
   Finite powers are exact; the coordinate isomorphism therefore makes tensor exact.
3. Exact tensor preserves quasi-isomorphisms on arbitrary unbounded complexes.
   The universal left-derived comparison consequently has invertible counit.
4. Apply the ordinary coordinates degreewise, compare finite powers of complexes,
   and descend through localization. Projection identities give the required
   normalization for the supplied counit, rather than a newly chosen derived functor.
5. Geometric module inverse image is exact. Its normalized underlying-sheaf
   comparisons supply the regular-module and restriction isomorphisms. Transport
   the basis using its product comparison, and use the scalar tower theorem for chi.
6. Test the ordinary coordinate square on pure tensors and product projections.
   Product preservation gives generalized elements in the inverse image of the
   scalar/module product. The balanced normalization of chi, the module-action
   normalization and the transported coordinate equation identify their images.
7. Descend chi with the two counits to obtain beta and its counit identity.
   Localization extensionality and product projections reduce the derived square
   to the ordinary square degreewise, using the restriction compositor normalization.
   All arguments apply to empty products and unbounded complexes.
-/
theorem derived_finiteFreeScalarCoordinates
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [E.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf R)) (.up ℤ))] :
    ∃ (_ : PreservesFiniteLimits (tensorFunctor a))
      (_ : PreservesFiniteColimits (tensorFunctor a))
      (_ : PreservesFiniteLimits (restriction.{u, u} a))
      (_ : PreservesFiniteColimits (restriction.{u, u} a))
      (_ : (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive)
      (_ : PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)))
      (_ : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))),
      (∀ {K L : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ}
        (f : K ⟶ L), QuasiIso f →
          QuasiIso (((tensorFunctor a).mapHomologicalComplex (.up ℤ)).map f)) ∧
      (∀ K : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ,
        IsIso (ε.app K)) ∧
      ∃ (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
          Functor.const (Discrete (Fin d)) ⋙ lim)
        (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
          Functor.const (Discrete (Fin d)) ⋙ lim),
        IsFiniteFreeScalarCoordinateIso a d θ φ ∧
        IsDerivedFiniteFreeScalarCoordinateIso a d E ε φ Φ ∧
        FiniteFreeCoordinatesInverseImage a d θ φ E ε Φ := by
  have := (restriction_exact a).1
  have := (restriction_exact a).2
  have := (extension_exact a d θ).1
  have := (extension_exact a d θ).2
  have : (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)) :=
    (SheafOfModules.power_exact _ d).2
  have := derivedCounit_isIso (tensorFunctor a) E ε
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, (fun _ ↦ inferInstance),
    ordinaryCoordinates a d θ,
    coordinateDescent (tensorFunctor a) (restriction a) d E ε (ordinaryCoordinates a d θ),
    ordinaryCoordinates_normalized a d θ,
    normalization_specialization a d E ε _ _
      (coordinateDescent_normalized (tensorFunctor a) (restriction a) d E ε
        (ordinaryCoordinates a d θ)), ?_⟩
  · intro K L f hf
    have : QuasiIso f := hf
    infer_instance
  · exact coordinates_inverseImage a d θ E ε
      _ (coordinateDescent_normalized (tensorFunctor a) (restriction a) d E ε
        (ordinaryCoordinates a d θ))

end SheafOfModules.RingedTensor
