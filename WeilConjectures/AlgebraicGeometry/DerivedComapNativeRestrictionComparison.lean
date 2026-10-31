/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.SectionModuleOperationsData
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.CategoryTheory.RightDerivedExactRestrictionNormalization
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Internal and native restriction/direct-image comparisons

Source: the latest blueprint, proper base change, rational proof paragraph (1),
and Stacks Project, Cohomology on Sites, Tag 0D6E; Modules on Sites, Tag 03D6.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison).

The identity section maps and their exact-localization factors are retained explicitly.
The coefficient identifications are specified by their adjuncts, so that the native
comparison below is the recorded ringed-topos comparison, not a chosen isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedComapNative

open ModuleRingedComparison

/-- The small-Hom section localization used by the recorded normalization theorem.
Source: Stacks 05RU. K-injective resolutions and local smallness shrink the standard
localization without changing its objects or its universal property.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
@[instance_reducible]
def sectionDerivedCategory {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u + 1}) :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} R) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      J R)

/-- Uniform access to the small-Hom localizations for the original normalization API.
Source: Stacks 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
@[instance_reducible]
def sectionDerivedCategories
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T) :=
  fun T ↦ sectionDerivedCategory (Scheme.ProEt.topology T) _

attribute [local instance] sectionDerivedCategory sectionDerivedCategories

/-- Expose the native standard localization at its actual Hom universe.
Source: Stacks 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
@[instance_reducible]
def nativeDerivedCategory {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The actual native derived category with its chosen localization passed explicitly.
The localization universe is an output parameter of instance search, so the small and
standard models must not be selected by competing instances.
Source: Stacks 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
abbrev nativeCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :=
  @DerivedCategory (modules Λ T) _ _
    (nativeDerivedCategory (Scheme.ProEt.topology T) _)

/-- Canonical localization of the identity, from the section normalization's small-Hom
model to the native standard model. Site objects and morphisms retain their sizes.
Source: Stacks 05RU, uniqueness of localization
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def localizationEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    DerivedCategory.{u + 1} (modules Λ T) ≌ nativeCategory Λ T :=
  @CategoryTheory.Equivalence.mapDerivedCategory (modules Λ T) (modules Λ T) _ _ _ _
    (sectionDerivedCategory (Scheme.ProEt.topology T) _)
    (nativeDerivedCategory (Scheme.ProEt.topology T) _)
    CategoryTheory.Equivalence.refl
    (inferInstanceAs (Functor.Additive (𝟭 (modules Λ T))))
    (inferInstanceAs (Functor.Additive (𝟭 (modules Λ T))))

/-- The fixed section equivalence, followed by canonical localization transport.
Source: Stacks 00YV and 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def sectionEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    DerivedCategory (internalModules Λ T) ≌ nativeCategory Λ T :=
  (derivedEquivalence Λ T).trans (localizationEquivalence Λ T)

/-- The already specified section equivalence is additive.
Source: Stacks 00YV
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
instance sectionAdditive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    (equivalence Λ T).functor.Additive :=
  sectionFunctorAdditive Λ T

/-- The section direct image is additive, as a right adjoint of module categories.
Source: Stacks 03D6
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
instance sectionPushAdditive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).Additive :=
  letI := (adjunction Λ f).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Canonical right-derived transport along the identity localization equivalences.
The factors are universal right-derived comparisons; on representatives they are
identities with the standard localization factors.
Source: Stacks 0D6E
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def localizationPushComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPushforward Λ f ⋙ (localizationEquivalence Λ Y).functor ≅
      (localizationEquivalence Λ X).functor ⋙
        (@Functor.rightDerivedFunctor (modules Λ X) (modules Λ Y) _ _ _ _
          (nativeDerivedCategory (Scheme.ProEt.topology X) _)
          (nativeDerivedCategory (Scheme.ProEt.topology Y) _) (pushforward Λ f) _ _) :=
  let transport
      {A B C D : Type (u + 2)}
      [Category.{u + 1} A] [Category.{u + 1} B]
      [Category.{u + 1} C] [Category.{u + 1} D]
      [Abelian A] [Abelian B] [Abelian C] [Abelian D]
      [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
      [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
      [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
      (F : A ⥤ B) (G : C ⥤ D) (eU : C ≌ A) (eV : D ≌ B)
      [F.Additive] [G.Additive] [eU.functor.Additive] [eV.functor.Additive]
      (c : F ⋙ eV.inverse ≅ eU.inverse ⋙ G) :
      F.rightDerivedFunctor ⋙ eV.inverse.mapDerivedCategory ≅
        eU.inverse.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F eV.inverse).symm ≪≫
      Functor.rightDerivedFunctorNatIso c ≪≫
        Functor.rightDerivedFunctorCompIso eU.inverse G ≪≫
          Functor.isoWhiskerRight eU.inverse.rightDerivedFunctorIsoMapDerivedCategory
            G.rightDerivedFunctor
  @transport
    (modules Λ X) (modules Λ Y) (modules Λ X) (modules Λ Y) _ _ _ _ _ _ _ _
    (sectionDerivedCategory (Scheme.ProEt.topology X) _)
    (sectionDerivedCategory (Scheme.ProEt.topology Y) _)
    (nativeDerivedCategory (Scheme.ProEt.topology X) _)
    (nativeDerivedCategory (Scheme.ProEt.topology Y) _) _ _
    (pushforward Λ f) (pushforward Λ f)
    CategoryTheory.Equivalence.refl CategoryTheory.Equivalence.refl _ _
    (inferInstanceAs (Functor.Additive (𝟭 (modules Λ X))))
    (inferInstanceAs (Functor.Additive (𝟭 (modules Λ Y))))
    (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- Register the recorded exact restriction theorem for the native functor.
Source: Stacks 05RT
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
instance nativeRestrictionFiniteLimits {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (b : R ⟶ S) :
    PreservesFiniteLimits (Scheme.proEtaleRingRestrictScalars b) :=
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits b

/-- Register the other half of the recorded exact restriction theorem.
Source: Stacks 05RT
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
instance nativeRestrictionFiniteColimits {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (b : R ⟶ S) :
    PreservesFiniteColimits (Scheme.proEtaleRingRestrictScalars b) :=
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits b

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The existing coefficient change on reconstructed section rings.
Source: Stacks 00YV and the coefficient-change square in the blueprint.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
abbrev scalarMap (T : Scheme.{u}) : ring Λ T ⟶ ring Λ' T :=
  CondensedRing.sectionRingMap T (ProEtale.coefficientMap a T)

/-- The existing exact termwise restriction on native module-sheaf derived categories.
Source: Stacks 03D6, 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
abbrev restriction (T : Scheme.{u}) :=
  @Functor.mapDerivedCategory (modules Λ' T) _ _
    (nativeDerivedCategory (Scheme.ProEt.topology T) _) (modules Λ T) _ _
    (nativeDerivedCategory (Scheme.ProEt.topology T) _)
    (Scheme.proEtaleRingRestrictScalars (scalarMap a T)) _ _ _

/-- Restriction commutes with canonical transport between the two localizations.
Source: Stacks 05RU, localization of the ordinary identity square
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def localizationRestrictionComparison (T : Scheme.{u}) :
    ((Scheme.proEtaleRingRestrictScalars (scalarMap a T)).mapDerivedCategory :
        DerivedCategory.{u + 1} (modules Λ' T) ⥤
          DerivedCategory.{u + 1} (modules Λ T)) ⋙
        (localizationEquivalence Λ T).functor ≅
      (localizationEquivalence Λ' T).functor ⋙ restriction a T :=
  @Functor.mapDerivedCategorySquareIso
    (modules Λ' T) (modules Λ T) (modules Λ' T) (modules Λ T) _ _ _ _ _ _ _ _
    (sectionDerivedCategory (Scheme.ProEt.topology T) _)
    (sectionDerivedCategory (Scheme.ProEt.topology T) _)
    (nativeDerivedCategory (Scheme.ProEt.topology T) _)
    (nativeDerivedCategory (Scheme.ProEt.topology T) _)
    (Scheme.proEtaleRingRestrictScalars (scalarMap a T)) (𝟭 (modules Λ T))
    (𝟭 (modules Λ' T)) (Scheme.proEtaleRingRestrictScalars (scalarMap a T))
    _ _ _ _ _ _ _ _ _ _ _ _
    (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- Localization of the existing identity-on-sections restriction square, followed
by canonical localization transport. The exact-localization factors are explicit.
Source: Stacks 00YV, 05RU
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def restrictionComparison (T : Scheme.{u}) :
    (Mod.comap (ProEtale.coefficientMap a T)).mapDerivedCategory ⋙
        (sectionEquivalence Λ T).functor ≅
      (sectionEquivalence Λ' T).functor ⋙ restriction a T :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategorySquareIso
      (F₁ := (Mod.comap (ProEtale.coefficientMap a T) :
        internalModules Λ' T ⥤ internalModules Λ T))
      (F₂ := (equivalence Λ T).functor) (G₁ := (equivalence Λ' T).functor)
      (G₂ := Scheme.proEtaleRingRestrictScalars (scalarMap a T))
      (CondensedRing.sectionModuleComapIso T (ProEtale.coefficientMap a T)))
    (localizationEquivalence Λ T).functor ≪≫
  Functor.isoWhiskerLeft (derivedEquivalence Λ' T).functor
    (localizationRestrictionComparison a T)

/-- The recorded section direct-image comparison, followed by the canonical native
identification. The equation hc specifies c as the section realization of alpha_f:
its adjoint is exactly the already constructed section-ring map induced by eta_f.
Source: Stacks 03D6 and 0D6E
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def pushComparison (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring Λ Y) ≅ ring Λ X)
    (hc : InternalModuleOperations.coefficientMap Λ f =
      ⟨Functor.whiskerRight
        (Scheme.proEtaleRingDirectImageMap f (ring Λ Y) (ring Λ X) c).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩) :
    (CondensedRing.moduleObjectDerivedPushforward Λ f) ⋙
        (sectionEquivalence Λ Y).functor ≅
      (sectionEquivalence Λ X).functor ⋙
        Scheme.proEtaleRingDerivedDirectImage f (ring Λ Y) (ring Λ X) c :=
  letI := InternalModuleOperations.siteMap_continuous f
  let e : pushforward Λ f ≅
      Scheme.proEtaleRingModuleDirectImage f (ring Λ Y) (ring Λ X) c :=
    SheafOfModules.pushforwardCongr hc
  Functor.isoWhiskerRight (derivedPushComparison Λ f)
      (localizationEquivalence Λ Y).functor ≪≫
    Functor.isoWhiskerLeft (derivedEquivalence Λ X).functor
      (localizationPushComparison Λ f) ≪≫
    Functor.isoWhiskerLeft (sectionEquivalence Λ X).functor
      (@Functor.rightDerivedFunctorNatIso (modules Λ X) (modules Λ Y) _ _ _ _
        (nativeDerivedCategory (Scheme.ProEt.topology X) _)
        (nativeDerivedCategory (Scheme.ProEt.topology Y) _) _ _ _ _ _ e)

/-- The section realization of alpha_f is the unique inverse-image ring identification
whose adjunct is the already fixed eta_f section-ring map.
Source: Stacks 00YV, 03D6; the coefficient identifications in the item statement.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison).
Proof: reconstruct the commutative ring map underlying eta_f, and transpose it under
inverse image/direct image for commutative ring sheaves. Reconstruction of ring objects
commutes with inverse image, since inverse image is strong monoidal and preserves
finite limits and colimits. After forgetting to abelian sheaves, this transpose is
alpha_f. Alpha_f is invertible; the forgetful ring-sheaf functor reflects isomorphisms,
so its transpose is an isomorphism. Transposing back gives the required equation.
The adjunction bijection and faithfulness of forgetting commutativity give uniqueness
of the hom, and therefore of the isomorphism. This works for every scheme morphism,
including identities and empty schemes, and for the zero coefficient ring. -/
theorem coefficientIdentification_existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring Λ Y) ≅
        ring Λ X,
      InternalModuleOperations.coefficientMap Λ f =
        ⟨Functor.whiskerRight
          (Scheme.proEtaleRingDirectImageMap f (ring Λ Y) (ring Λ X) c).hom
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
  sorry

/-- The actual section-ring realization of alpha_f, selected by its unique adjunct
normalization. The preceding theorem determines the object uniquely, not merely up
to an unspecified isomorphism.
Source: Stacks 00YV, 03D6
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def coefficientIdentification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring Λ Y) ≅ ring Λ X :=
  (coefficientIdentification_existsUnique Λ f).exists.choose

/-- The coefficient-change square for the canonical section realization of alpha.
Source: the blueprint coefficient-change square; Stacks 03D6.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison).
Proof: transpose both morphisms under the ring-sheaf inverse-image adjunction.
Their adjuncts are eta'_f after a_Y and f_*(a_X) after eta_f, by the two defining
normalization equations and adjunction naturality. The recorded coefficient-change
square identifies these maps on underlying abelian sheaves. Reconstruction of ring
maps and forgetting commutativity are faithful, so the adjuncts agree as ring maps.
Injectivity of the adjunction bijection gives the displayed equality. -/
theorem coefficientIdentification_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coefficientIdentification Λ f).hom ≫ scalarMap a X =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (scalarMap a Y) ≫
        (coefficientIdentification Λ' f).hom := by
  sorry

/-- The specified sigma, in the canonical native ring-sheaf coordinates.
Source: Stacks 0D6E and section-derived push-pull normalization.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
abbrev sigma (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pushComparison Λ f (coefficientIdentification Λ f)
    (coefficientIdentification_existsUnique Λ f).exists.choose_spec

/-- The recorded native d, specialized to the actual section-ring realizations.
Source: Stacks 0D6E
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
abbrev nativeComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (ring Λ Y) (ring Λ' Y) (ring Λ X) (ring Λ' X)
    (scalarMap a Y) (scalarMap a X)
    (coefficientIdentification Λ f) (coefficientIdentification Λ' f)
    (coefficientIdentification_square a f)

variable [∀ T : Scheme.{u}, PreservesFiniteLimits
  (Mod.extendScalars (ProEtale.coefficientMap a T))]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The specified native d, read in internal coordinates by the fixed fully faithful
section equivalence. Every factor is a recorded comparison or its inverse; no
isomorphism is selected from a mere existence assertion.
Source: Stacks 0D6E and blueprint rational proper base change, paragraph (1).
(blueprint: lem-sfb-derived-comap-native-restriction-comparison). -/
def transportedNativeComparison :
    CondensedRing.moduleObjectDerivedPushforward Λ' f ⋙
        (Mod.comap (ProEtale.coefficientMap a Y)).mapDerivedCategory ≅
      (Mod.comap (ProEtale.coefficientMap a X)).mapDerivedCategory ⋙
        CondensedRing.moduleObjectDerivedPushforward Λ f :=
  ((sectionEquivalence Λ Y).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CondensedRing.moduleObjectDerivedPushforward Λ' f)
        (restrictionComparison a Y) ≪≫
      Functor.isoWhiskerRight (sigma Λ' f) (restriction a Y) ≪≫
      Functor.isoWhiskerLeft (sectionEquivalence Λ' X).functor
        (nativeComparison a f) ≪≫
      Functor.isoWhiskerRight (restrictionComparison a X).symm
        (Scheme.proEtaleRingDerivedDirectImage f (ring Λ Y) (ring Λ X)
          (coefficientIdentification Λ f)) ≪≫
      Functor.isoWhiskerLeft (Mod.comap (ProEtale.coefficientMap a X)).mapDerivedCategory
        (sigma Λ f).symm)

/-- Internal restriction/direct image agrees with the native ringed-topos comparison;
its scalar-extension mate is consequently the mate of the inverse native comparison.
The coefficient identifications are the unique section realizations of alpha_f and
alpha'_f; their adjuncts are exactly eta_f and eta'_f on section rings.

Source: latest blueprint, rational proper base change, paragraph (1);
Stacks Project, Cohomology on Sites, Tag 0D6E; Modules on Sites, Tag 03D6.
(blueprint: lem-sfb-derived-comap-native-restriction-comparison).

Proof:
1. The fixed section equivalence preserves sections and restrictions. Both ordinary
   restriction/direct-image paths act on N(X times_Y W) through the same scalar map:
   eta'_f a_Y = f_*(a_X) eta_f. Their comparisons, including the section pushforward
   comparisons, are identities on that section group. Thus the ordinary cube commutes
   degreewise, including its differentials (the coefficient-change square).
2. Choose a K-injective representative I of M. The flat extension hypothesis makes
   internal restriction preserve K-injectivity. The section equivalence and its exact
   inverse preserve and reflect K-injectivity and resolutions by section normalization.
   Hence I, Res(I), E(I), and E(Res(I)) compute all four derived direct images. Use the
   canonical exact-localization factors for the two restrictions and the equivalences.
3. The right-derived exact-restriction normalization computes the specified internal
   derivedComapLowerStarIso as the ordinary identity comparison on I: its equation
   with the right-derived units pins it, and these units are invertible on I and Res(I).
4. Section-derived push-pull normalization computes both specified pushComparison
   maps as the ordinary identity-on-sections maps on these representatives. Naturality
   moves the exact-localization factors across the comparison for Res(I).
5. For native d use its normalized ringed direct-image composition construction.
   On the route through the target scalar restriction, a further K-injective resolution
   j of f_*E(I) contributes restriction(j). Exact restriction makes this invertible;
   the exact-functor/right-derived identification cancels it. On the other route,
   Res(E(I)) is already K-injective, so the further resolution is the identity. Thus
   d is represented by the ordinary identity comparison. No K-injectivity of f_*E(I)
   is needed. The ordinary equality of step 1 gives the displayed equality at Q(I).
6. Naturality along an isomorphism M to Q(I), and cancellation of its image, give
   equality at every M. Full faithfulness identifies the transported native comparison
   with the specified internal comparison.
7. derivedPushHom is the mate of the inverse internal comparison, namely the target
   scalar counit composed with extension of that inverse and the source scalar unit.
   Substitute the equality from step 6 in this formula. This is exactly the mate of
   inverse d under the same coordinate identifications, as in the second conjunct. -/
theorem derivedComap_native_restriction_comparison :
    (∀ M : DerivedCategory (internalModules Λ' X),
      (sectionEquivalence Λ Y).functor.map
          ((CondensedRing.derivedComapLowerStarIso a f).hom.app M) ≫
        (sigma Λ f).hom.app
          ((Mod.comap (ProEtale.coefficientMap a X)).mapDerivedCategory.obj M) ≫
        (Scheme.proEtaleRingDerivedDirectImage f (ring Λ Y) (ring Λ X)
          (coefficientIdentification Λ f)).map
          ((restrictionComparison a X).hom.app M) =
      (restrictionComparison a Y).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj M) ≫
        (restriction a Y).map ((sigma Λ' f).hom.app M) ≫
        (nativeComparison a f).hom.app
            ((sectionEquivalence Λ' X).functor.obj M)) ∧
    CondensedRing.derivedPushHom a f =
      Adjunction.pushHomOfComapIso
        (Mod.derivedExtendMapDerivedCategoryAdjunction (ProEtale.coefficientMap a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (ProEtale.coefficientMap a Y))
        (transportedNativeComparison a f) := by
  sorry

end AlgebraicGeometry.ProEtale.DerivedComapNative
