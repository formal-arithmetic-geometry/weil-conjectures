/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType

import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedCoefficientRestrictionCounit
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
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
import WeilConjectures.AlgebraicGeometry.EtaleRelativeFrobeniusIso
import WeilConjectures.CategoryTheory.RightDerivedPlusCube

/-! # Relative derived étale/Zariski comparison

Source: Stacks Project, Descent Tag 071N; Étale Cohomology Tag 03P2;
Cohomology of Schemes Tag 02KH; Cohomology on Sites Tags 0736 and 07A8;
Étale Morphisms Tag 0EBS
(blueprint: lem-fd-qcoherent-relative-etale-zariski-derived).

The comparison is the bounded-below derived base-change map of the ordinary
adjunction mate, followed by the exact-forgetful coefficient comparison. Its ordinary
square is normalized on sections. The auxiliary records retain actual ringed-topos
morphisms and exactness proofs; they contain no unspecified comparison proposition.
Frobenius transport is normalized on tensor generators before it is derived.
Abelian coefficients are canonically lifted once to universe u+1, as in the project's
small étale derived-functor framework; module coefficients and schemes remain in u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard localization for the underlying module-sheaf presentation.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
instance relativeModuleDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u+1} (SheafOfModules.{u} T.ringCatSheaf) :=
  HasDerivedCategory.standard (SheafOfModules.{u} T.ringCatSheaf)
/-- The same localization in the Scheme.Modules presentation; no second choice is made.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
instance relativeSchemeDerived (T : Scheme.{u}) : HasDerivedCategory.{u+1} T.Modules :=
  relativeModuleDerived T
/-- Enough injectives for module sheaves on the underlying ringed space.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
instance relativeModuleInjectives (T : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} T.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives T.toRingedSpace).2
/-- The ringed-space enough-injectives proof in the Scheme.Modules presentation.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
instance relativeSchemeInjectives (T : Scheme.{u}) : EnoughInjectives T.Modules :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives T.toRingedSpace).2
/-- Mathlib restriction of scalars, with its domain and codomain presented as Scheme.Modules. This
changes no objects, maps or scalar actions.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def relativeZariskiRestrictScalars (T : Scheme.{u})
    (sigma : T.ringCatSheaf ⟶ T.ringCatSheaf) : T.Modules ⥤ T.Modules :=
  SheafOfModules.restrictScalars.{u} sigma
/-- Additivity transported from the existing restriction-of-scalars functor.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
instance relativeRestrictScalarsAdditive (T : Scheme.{u})
    (sigma : T.ringCatSheaf ⟶ T.ringCatSheaf) :
    (relativeZariskiRestrictScalars T sigma).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u} sigma).Additive
/-- Abelian sheaves on the actual small étale site, with the common u+1 coefficient universe.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
abbrev RelativeEtaleAbelianSheaves (T : Scheme.{u}) := Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u+1}
/-- Forget the structure-sheaf action and apply the canonical sectionwise universe lift.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def relativeEtaleForgetModules (T : Scheme.{u}) : SmallEtaleModules T ⥤
  RelativeEtaleAbelianSheaves T :=
  SheafOfModules.toSheaf (smallEtaleModuleRing T) ⋙
    sheafCompose T.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u+1,u}
/-- Presented canonical change-of-topology morphisms and their flat direct-image square. The
epsilon module direct images are the existing open-restriction functors. The right square is
fixed on every section; the ordinary comparison is its tensor-adjunction mate followed by the
sectionwise identity coefficient comparison. All exactness fields are conclusions to be supplied
by the theorem, rather than assumptions on f or F.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
structure RelativeEtaleZariskiContext {X S : Scheme.{u}} (f : X ⟶ S) where
  source : ZariskiEtaleModuleContext X
  target : ZariskiEtaleModuleContext S
  [source_additive : source.extension.Additive]
  [target_additive : target.extension.Additive]
  [source_limits : PreservesFiniteLimits source.extension]
  [source_colimits : PreservesFiniteColimits source.extension]
  [target_limits : PreservesFiniteLimits target.extension]
  [target_colimits : PreservesFiniteColimits target.extension]
  [source_ab_additive : (source.extension ⋙ relativeEtaleForgetModules X).Additive]
  [target_ab_additive : (target.extension ⋙ relativeEtaleForgetModules S).Additive]
  [source_ab_limits : PreservesFiniteLimits (source.extension ⋙ relativeEtaleForgetModules X)]
  [source_ab_colimits : PreservesFiniteColimits (source.extension ⋙ relativeEtaleForgetModules X)]
  [target_ab_limits : PreservesFiniteLimits (target.extension ⋙ relativeEtaleForgetModules S)]
  [target_ab_colimits : PreservesFiniteColimits (target.extension ⋙ relativeEtaleForgetModules S)]
  [source_forget_rings : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [source_forget_groups :
    X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [target_forget_rings : S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [target_forget_groups :
    S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  source_epsilon :
    RingedToposMorphismOnSites.{u, u+1, u, u, u} (smallEtaleModuleRing X) X.ringCatSheaf
  target_epsilon :
    RingedToposMorphismOnSites.{u, u+1, u, u, u} (smallEtaleModuleRing S) S.ringCatSheaf
  source_epsilon_modules : source_epsilon.modules = source.restriction
  target_epsilon_modules : target_epsilon.modules = target.restriction
  source_epsilon_direct_maps : ∀ (M N : Sheaf X.smallEtaleTopology (Type u)) (g : M ⟶ N),
    HEq (source_epsilon.direct.map g).hom
      (Functor.whiskerLeft (AlgebraicGeometry.gabberOpenEtale X).op g.hom)
  target_epsilon_direct_maps : ∀ (M N : Sheaf S.smallEtaleTopology (Type u)) (g : M ⟶ N),
    HEq (target_epsilon.direct.map g).hom
      (Functor.whiskerLeft (AlgebraicGeometry.gabberOpenEtale S).op g.hom)
  source_epsilon_direct : ∀ M : Sheaf X.smallEtaleTopology (Type u),
    (source_epsilon.direct.obj M).obj =
      (AlgebraicGeometry.gabberOpenEtale X).op ⋙ M.obj
  target_epsilon_direct : ∀ M : Sheaf S.smallEtaleTopology (Type u),
    (target_epsilon.direct.obj M).obj =
      (AlgebraicGeometry.gabberOpenEtale S).op ⋙ M.obj
  source_associated : ∀ (M : X.Modules) [M.IsQuasicoherent],
    (SheafOfModules.toSheaf (smallEtaleModuleRing X)).obj (source.extension.obj M) ≅
      etaleTensorSectionsSheaf M
  source_associated_linear : ∀ (M : X.Modules) [M.IsQuasicoherent] (V : X.Etale)
      (b : (smallEtaleModuleRing X).obj.obj (op V))
      (m : (source.extension.obj M).val.obj (op V)),
    (source_associated M).hom.hom.app (op V) (b • m) =
      b • @id (((tensorPullback V.hom).obj M).val.obj (op ⊤))
        ((source_associated M).hom.hom.app (op V) m)
  source_associated_sections : ∀ (M : X.Modules) [M.IsQuasicoherent]
      (W : X.Opens) (m : M.val.obj (op W)),
    ((source_associated M).hom.hom.app
      (op ((AlgebraicGeometry.gabberOpenEtale X).obj W)))
        ((source.adjunction.unit.app M).app W m) =
      (tensorOpenSectionIso X M W).inv m
  target_associated : ∀ (M : S.Modules) [M.IsQuasicoherent],
    (SheafOfModules.toSheaf (smallEtaleModuleRing S)).obj (target.extension.obj M) ≅
      etaleTensorSectionsSheaf M
  target_associated_linear : ∀ (M : S.Modules) [M.IsQuasicoherent] (V : S.Etale)
      (b : (smallEtaleModuleRing S).obj.obj (op V))
      (m : (target.extension.obj M).val.obj (op V)),
    (target_associated M).hom.hom.app (op V) (b • m) =
      b • @id (((tensorPullback V.hom).obj M).val.obj (op ⊤))
        ((target_associated M).hom.hom.app (op V) m)
  target_associated_sections : ∀ (M : S.Modules) [M.IsQuasicoherent]
      (W : S.Opens) (m : M.val.obj (op W)),
    ((target_associated M).hom.hom.app
      (op ((AlgebraicGeometry.gabberOpenEtale S).obj W)))
        ((target.adjunction.unit.app M).app W m) =
      (tensorOpenSectionIso S M W).inv m
  etale_right : (smallEtaleModulePushforward f).IsRightAdjoint
  ordinary_right : smallEtaleModulePushforward f ⋙ target.restriction ≅
    source.restriction ⋙ pushforward f
  ordinary_right_sections : ∀ (G : SmallEtaleModules X) (W : S.Opens),
    (ordinary_right.hom.app G).app W =
      G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso f W).hom.op
  forget_direct : smallEtaleModulePushforward f ⋙ relativeEtaleForgetModules S ≅
    relativeEtaleForgetModules X ⋙ Etale.lowerStar AddCommGrpCat.{u+1} f
  forget_direct_sections : ∀ (M : SmallEtaleModules X) (V : S.Etale)
      (m : ((smallEtaleModulePushforward f).obj M).val.obj (op V)),
    (forget_direct.hom.app M).hom.app (op V) (ULift.up m) = ULift.up m
  ordinary : pushforward f ⋙ (target.extension ⋙ relativeEtaleForgetModules S) ⟶
    (source.extension ⋙ relativeEtaleForgetModules X) ⋙ Etale.lowerStar AddCommGrpCat.{u+1} f
  ordinary_normalized : ∀ M : X.Modules,
    ordinary.app M = (relativeEtaleForgetModules S).map
      (zariskiEtalePushforwardComparison f source target etale_right ordinary_right M) ≫
        forget_direct.hom.app (source.extension.obj M)
attribute [instance] RelativeEtaleZariskiContext.source_additive
  RelativeEtaleZariskiContext.target_additive
  RelativeEtaleZariskiContext.source_limits RelativeEtaleZariskiContext.source_colimits
  RelativeEtaleZariskiContext.target_limits RelativeEtaleZariskiContext.target_colimits
  RelativeEtaleZariskiContext.source_ab_additive RelativeEtaleZariskiContext.target_ab_additive
  RelativeEtaleZariskiContext.source_ab_limits RelativeEtaleZariskiContext.source_ab_colimits
  RelativeEtaleZariskiContext.target_ab_limits RelativeEtaleZariskiContext.target_ab_colimits
variable {X S : Scheme.{u}} {f : X ⟶ S}
/-- The exact functor U_X epsilon_X^* applied levelwise to bounded-below derived objects.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.sourceDerived (c : RelativeEtaleZariskiContext f) :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus (RelativeEtaleAbelianSheaves X) :=
  letI := c.source_ab_additive
  letI := c.source_ab_limits
  letI := c.source_ab_colimits
  (c.source.extension ⋙ relativeEtaleForgetModules X).mapDerivedCategoryPlus

/-- The exact functor U_S epsilon_S^* applied levelwise to bounded-below derived objects.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.targetDerived (c : RelativeEtaleZariskiContext f) :
    DerivedCategory.Plus S.Modules ⥤ DerivedCategory.Plus (RelativeEtaleAbelianSheaves S) :=
  letI := c.target_ab_additive
  letI := c.target_ab_limits
  letI := c.target_ab_colimits
  (c.target.extension ⋙ relativeEtaleForgetModules S).mapDerivedCategoryPlus

/-- The canonical flat-square derived comparison. It is the generic
rightDerivedFunctorPlusBaseChange of the unit/counit-normalized ordinary mate, so its
derived-unit normalization is fixed by rightDerivedFunctorPlusBaseChange_fac.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.comparison (c : RelativeEtaleZariskiContext f) :
    (pushforward f).rightDerivedFunctorPlus ⋙ c.targetDerived ⟶
      c.sourceDerived ⋙ (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus :=
  letI := c.source_ab_additive
  letI := c.source_ab_limits
  letI := c.source_ab_colimits
  letI := c.target_ab_additive
  letI := c.target_ab_limits
  letI := c.target_ab_colimits
  Functor.rightDerivedFunctorPlusBaseChange c.ordinary

/-- The canonical compatibility of exact change of topology and forgetting with a module in degree
zero.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.sourceSingle (c : RelativeEtaleZariskiContext f) (M : X.Modules) :
    c.sourceDerived.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).obj
        ((c.source.extension ⋙ relativeEtaleForgetModules X).obj M) :=
  letI := c.source_ab_additive
  letI := c.source_ab_limits
  letI := c.source_ab_colimits
  ((c.source.extension ⋙ relativeEtaleForgetModules X).mapDerivedCategoryPlusSingleFunctor 0).app M

/-- The canonical relative comparison in D^+(Ab(S_Et)), with F placed in degree zero. The source
uses module derived Zariski direct image; the target uses abelian derived étale direct image.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.arrow (c : RelativeEtaleZariskiContext f) (M : X.Modules) :
    c.targetDerived.obj ((pushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).obj
          ((c.source.extension ⋙ relativeEtaleForgetModules X).obj M)) :=
  c.comparison.app ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
    (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
      (c.sourceSingle M).hom



/-- Frobenius restriction of scalars and its étale tensor transport. The ring map and linear
structure-module map are p-th powers on every open. The natural isomorphism is fixed on all
local tensor generators by b tensor m ↦ b^p tensor m, including arbitrary modules. These
normalizations prevent a free choice of a Frobenius endomorphism.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
structure RelativeEtaleZariskiFrobeniusTransport {T : Scheme.{u}}
    (c : ZariskiEtaleModuleContext T) (p : ℕ) where
  sigma : T.ringCatSheaf ⟶ T.ringCatSheaf
  sigma_sections : ∀ (W : T.Opens) (a : T.ringCatSheaf.obj.obj (op W)),
    (sigma.hom.app (op W)) a = a ^ p
  [res_limits : PreservesFiniteLimits (relativeZariskiRestrictScalars T sigma)]
  [res_colimits : PreservesFiniteColimits (relativeZariskiRestrictScalars T sigma)]
  twist : relativeZariskiRestrictScalars T sigma ⋙ (c.extension ⋙ relativeEtaleForgetModules T) ≅
    c.extension ⋙ relativeEtaleForgetModules T
  twist_generators : ∀ (M : T.Modules) (W : T.Opens) (V : T.Etale)
      (j : V ⟶ (AlgebraicGeometry.gabberOpenEtale T).obj W)
      (b : (smallEtaleModuleRing T).obj.obj (op V)) (m : M.val.obj (op W)),
    (twist.hom.app M).hom.app (op V)
      (ULift.up (b • (c.extension.obj
        ((relativeZariskiRestrictScalars T sigma).obj M)).val.map j.op
          ((c.adjunction.unit.app ((relativeZariskiRestrictScalars T sigma).obj M)).app W m))) =
      ULift.up (b ^ p • (c.extension.obj M).val.map j.op
        ((c.adjunction.unit.app M).app W m))
  linear : SheafOfModules.unit T.ringCatSheaf ⟶
    (relativeZariskiRestrictScalars T sigma).obj (SheafOfModules.unit T.ringCatSheaf)
  linear_sections : ∀ (W : T.Opens) (a : T.ringCatSheaf.obj.obj (op W)),
    linear.val.app (op W) a = a ^ p

/-- Exact restriction of scalars along the sectionwise Frobenius, on D^+ of Zariski modules.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiFrobeniusTransport.resDerived {T : Scheme.{u}}
    {c : ZariskiEtaleModuleContext T} {p : ℕ} (t : RelativeEtaleZariskiFrobeniusTransport c p) :
    DerivedCategory.Plus T.Modules ⥤ DerivedCategory.Plus T.Modules :=
  letI := t.res_limits
  letI := t.res_colimits
  (relativeZariskiRestrictScalars T t.sigma).mapDerivedCategoryPlus

/-- The canonical derived exchange between direct image and Frobenius scalar restriction, obtained
from their ordinary sectionwise identity square.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def relativeEtaleZariskiResDerivedComparison (c : RelativeEtaleZariskiContext f) {p : ℕ}
    (x : RelativeEtaleZariskiFrobeniusTransport c.source p)
    (s : RelativeEtaleZariskiFrobeniusTransport c.target p)
    (r : pushforward f ⋙ relativeZariskiRestrictScalars S s.sigma ≅
      relativeZariskiRestrictScalars X x.sigma ⋙ pushforward f) :
    (pushforward f).rightDerivedFunctorPlus ⋙ s.resDerived ⟶
      x.resDerived ⋙ (pushforward f).rightDerivedFunctorPlus :=
  letI := x.res_limits
  letI := x.res_colimits
  letI := s.res_limits
  letI := s.res_colimits
  Functor.rightDerivedFunctorPlusBaseChange
    (B := X.Modules) (B' := X.Modules) (C := S.Modules) (C' := S.Modules) r.hom

/-- The Frobenius scalar-restriction square for f. Its ordinary comparison is the identity on all
sections and its derived comparison is required to be invertible; thus the inverse used below is
determined.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
structure RelativeEtaleZariskiFrobeniusSquare (c : RelativeEtaleZariskiContext f) (p : ℕ) where
  source : RelativeEtaleZariskiFrobeniusTransport c.source p
  target : RelativeEtaleZariskiFrobeniusTransport c.target p
  ordinary : pushforward f ⋙ relativeZariskiRestrictScalars S target.sigma ≅
    relativeZariskiRestrictScalars X source.sigma ⋙ pushforward f
  ordinary_sections : ∀ (M : X.Modules) (W : S.Opens)
      (m : ((pushforward f).obj M).val.obj (op W)),
    (ordinary.hom.app M).val.app (op W) m = m
  derived_iso : IsIso (relativeEtaleZariskiResDerivedComparison c source target ordinary)



/-- The exact-functor lift of the tensor-normalized étale Frobenius transport, using the canonical
composition isomorphism for derived exact functors.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.targetTwist (c : RelativeEtaleZariskiContext f) {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusTransport c.target p) :
    t.resDerived ⋙ c.targetDerived ≅ c.targetDerived :=
  letI := t.res_limits
  letI := t.res_colimits
  letI := c.target_ab_additive
  letI := c.target_ab_limits
  letI := c.target_ab_colimits
  letI := c.target_additive
  (Functor.mapDerivedCategoryPlusCompIso (relativeZariskiRestrictScalars S t.sigma)
    (c.target.extension ⋙ relativeEtaleForgetModules S)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso t.twist

/-- Additive Frobenius on U_S epsilon_S^* Rf_Zar,* O_X. First derive O_X → Res_F O_X, use the
inverse of the canonical direct-image/scalar-restriction exchange, and then apply the
tensor-normalized étale transport. This construction is independent of the relative comparison
arrow.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiFrobeniusSquare.sourceAction {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) :
    c.targetDerived.obj ((pushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf))) ⟶
    c.targetDerived.obj ((pushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf))) :=
  letI := t.source.res_limits
  letI := t.source.res_colimits
  letI := t.target.res_limits
  letI := t.target.res_colimits
  letI := t.derived_iso
  c.targetDerived.map
    ((pushforward f).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map t.source.linear ≫
        ((relativeZariskiRestrictScalars X t.source.sigma).mapDerivedCategoryPlusSingleFunctor
          0).inv.app (SheafOfModules.unit X.ringCatSheaf)) ≫
      (inv (relativeEtaleZariskiResDerivedComparison c t.source t.target t.ordinary)).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf))) ≫
    (c.targetTwist t.target).hom.app ((pushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)))

/-- Additive Frobenius on Rf_Et,*^Ab(U_X epsilon_X^* O_X). Apply abelian derived direct image to
the sectionwise Frobenius obtained from the linear map to scalar restriction and its
tensor-normalized transport.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiFrobeniusSquare.targetAction {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) :
    (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).obj
        ((c.source.extension ⋙ relativeEtaleForgetModules X).obj (SheafOfModules.unit
          X.ringCatSheaf))) ⟶
    (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).obj
        ((c.source.extension ⋙ relativeEtaleForgetModules X).obj (SheafOfModules.unit
          X.ringCatSheaf))) :=
  (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).map
      ((c.source.extension ⋙ relativeEtaleForgetModules X).map t.source.linear ≫
        t.source.twist.hom.app (SheafOfModules.unit X.ringCatSheaf)))

/-- Identify H^q of U_S epsilon_S^* Rf_Zar,* M[0] with U_S epsilon_S^* R^q f_Zar,* M, using the
existing derived-functor cohomology and exact-functor isomorphisms.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiContext.homologyIdentification (c : RelativeEtaleZariskiContext f) (M :
  X.Modules) (q : ℕ) :
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj (((pushforward f).rightDerived q).obj
      M) ≅
      (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).obj
        (c.targetDerived.obj ((pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) :=
  letI := c.target_ab_additive
  letI := c.target_ab_limits
  letI := c.target_ab_colimits
  (c.target.extension ⋙ relativeEtaleForgetModules S).mapIso
    (((pushforward f).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).app
      M).symm ≪≫
    ((c.target.extension ⋙ relativeEtaleForgetModules S).mapDerivedCategoryPlusHomologyFunctorIso
      q).app
      ((pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))

/-- The induced Frobenius on the actual extended higher direct-image sheaf: transport the
cohomology of sourceAction through the canonical homology identification.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiFrobeniusSquare.homologyAction {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) (q : ℕ) :
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj
      (((pushforward f).rightDerived q).obj (SheafOfModules.unit X.ringCatSheaf)) ⟶
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj
      (((pushforward f).rightDerived q).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (c.homologyIdentification (SheafOfModules.unit X.ringCatSheaf) q).hom ≫
    (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).map t.sourceAction ≫
      (c.homologyIdentification (SheafOfModules.unit X.ringCatSheaf) q).inv



/-- The induced Frobenius on local sections of epsilon_S^* R^q f_* O_X. Lift the input, apply
homologyAction, and take the underlying section; no scalar action is defined by the desired
semilinearity equation.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).
-/
def RelativeEtaleZariskiFrobeniusSquare.sectionAction {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) (q : ℕ) (V : S.Etale)
    (e : (c.target.extension.obj (((pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)) :
    (c.target.extension.obj (((pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V) :=
  ((t.homologyAction q).hom.app (op V) (ULift.up e)).down

/-- Relative quasi-coherent derived étale/Zariski comparison, natural in all O_X-linear maps F → G,
with additive Frobenius compatibility in characteristic p and its semilinearity on every étale
object's local sections. The existential context supplies only canonical presented constructions
and their normalizations; the comparison itself is the explicitly defined arrow above.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).

Proof: 1. Apply [lem-fd-etale-zariski-ringed-pullback-flat] for \(T=X,S\). It gives exactness on
all modules, not merely on the quasi-coherent subcategory, and the canonical identifications
\(\epsilon_X^*\mathcal F=\mathcal F_{\mathrm{Et}}\). Put \(K=Rf_{\mathrm{Zar},*}(\mathcal
F[0])\) and \(L=Rf_{\mathrm{Et},*}^{\mathrm{Mod}}(\mathcal F_{\mathrm{Et}}[0])\). By
[lem-pc-sections-higher-direct-image-quasi-coherent], every \(\mathcal H^qK\) is quasi-coherent.
Exact pullback commutes with cohomology by [lem-weil-pbc-exact-functor-bounded-below], so
\(\epsilon_S^*K\) lies in the étale \(D^+_{\mathrm{QC}}\). Choose the small skeleta and common
module universe of [def-weil-size-convention]; [prop-pur-kinjective-resolutions-exist] supplies
module resolutions.

2. Using the sectionwise direct image of [def-weil-pbc-direct-image], the square of small ringed
topoi with top edge \(\epsilon_X\), bottom edge \(\epsilon_S\), and vertical edges
\(f_{\mathrm{Et}},f_{\mathrm{Zar}}\) commutes: restricting étale direct image to an open
\(W\subset S\) evaluates on \(X\times_SW=f^{-1}W\), with the same structural ring maps. Its
horizontal edges are flat by [lem-fd-etale-zariski-ringed-pullback-flat]. Thus
[lem-fd-flat-ringed-square-derived-mate] defines the canonical module comparison
\(\beta:\epsilon_S^*K\to L\). This also fixes its meaning, rather than choosing arbitrary
isomorphisms on cohomology groups.

3. Show \(L\in D^+_{\mathrm{QC}}\). By [lem-pur-ringed-coefficient-restriction-counit] with
constant coefficient ring \(\mathbf Z\), forgetting modules identifies its derived direct image
with the abelian one. By [lem-weil-pbc-higher-direct-image-sheafified-presheaf], its
degree-\(q\) cohomology is the sheafification of \(V\mapsto H^q_{\mathrm{Et}}(X_V,\mathcal
F_V)\), where \(V\to S\) is étale, \(X_V=X\times_SV\), and \(\mathcal F_V\) is the pulled-back
quasi-coherent module. The base change is an étale object by
[lem-weil-pbc-etale-base-change-finite-limits]. The cohomology-over-an-object is the cohomology
on the small site of \(X_V\), by [lem-weil-pbc-cohomology-over-object-localization] and
[lem-weil-pbc-etale-site-localization-open]. Pullback preserves quasi-coherence by
[lem-weil-pbc-module-pullback-quasi-coherent]. Module and abelian evaluations agree by
[lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison]. The absolute derived unit
comparison [lem-fd-etale-zariski-qcoherent-derived-unit] identifies this presheaf canonically
with \(V\mapsto H^q_{\mathrm{Zar}}(X_V,\mathcal F_V)\), compatibly with the restriction maps and
scalar actions.

4. For an affine étale \(v:V\to S\), flatness follows from [def-weil-etale-morphism], and flat
base change [lem-pc-flat-base-change-cohom] gives \(v^*R^qf_{\mathrm{Zar},*}\mathcal F\cong
R^q(f_V)_*\mathcal F_V\). The latter has quasi-coherent cohomology by
[lem-pc-sections-higher-direct-image-quasi-coherent], since [lem-pc-quasi-compact-base-change]
applies to \(f\) and its quasi-compact diagonal; the diagonal of \(f_V\) is the base change of
that diagonal, so it too is quasi-compact, as required by [def-weil-quasi-separated-morphism].
Affine vanishing [lem-pc-affine-vanishing] and the cocycle-normalized edge isomorphism
[lem-pc-leray-degenerate-sections] give \(H^q(X_V,\mathcal F_V)\cong\Gamma(V,R^q(f_V)_*\mathcal
F_V)\). These are the canonical edge and base-change maps, so their restrictions along an affine
étale \(V'\to V\) agree: both send a restricted cocycle to its class in the pulled-back
cohomology sheaf. Thus on the affine basis the presheaf in Step 3 is canonically
\(V\mapsto\Gamma(V,v^*R^qf_*\mathcal F)\). Its sheafification is \((R^qf_*\mathcal
F)_{\mathrm{Et}}\) by [def-sc-etale-qcoherent-module]. This proves the required quasi-coherence
of \(\mathcal H^qL\); negative cohomology vanishes by right-derived bounded-below construction.
Affine objects suffice: cover any étale object by affine opens, whose inclusions are étale by
[lem-weil-pbc-open-immersion-etale]; refine overlaps by affine opens again. The
restriction-compatible affine identifications therefore glue uniquely after sheafification by
the sheaf axiom.

5. Apply \(R\epsilon_{S,*}\) to \(\beta\). Under the derived composition isomorphisms
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], its adjoint is the composite
\(K\xrightarrow{Rf_{\mathrm{Zar},*}\eta_X}Rf_{\mathrm{Zar},*}R\epsilon_{X,*}\epsilon_X^*\mathcal
F\cong R\epsilon_{S,*}L\). The unit formula of [lem-fd-flat-ringed-square-derived-mate] says
precisely \(R\epsilon_{S,*}(\beta)\circ\eta_{S,K}=Rf_{\mathrm{Zar},*}(\eta_{X,\mathcal F})\).
Both units are isomorphisms by [lem-fd-etale-zariski-qcoherent-derived-unit]; for \(K\) use its
quasi-coherent cohomology from Step 1. Hence \(R\epsilon_{S,*}\beta\) is invertible. Since both
ends of \(\beta\) are in \(D^+_{\mathrm{QC}}\) by Steps 1 and 4, the same absolute equivalence
reflects isomorphisms and proves \(\beta\) invertible. This proves the chosen derived map is an
isomorphism, not only existence of per-degree identifications.

6. Use [lem-pur-ringed-coefficient-restriction-counit] for \(f_{\mathrm{Et}}\) and \(A=\mathbf
Z\) to compose \(U_S\beta\) with its canonical isomorphism \(U_SL\cong
Rf_{\mathrm{Et},*}^{\mathrm{Ab}}U_X\mathcal F_{\mathrm{Et}}\). Its normalization by derived
composition identifies this with the canonical relative comparison in the statement. Forgetting
is exact because kernels are sectionwise and cokernels are sheafified cokernels in
[def-weil-sheaf-of-modules-category]. Naturality follows from the naturality in the argument of
[lem-fd-flat-ringed-square-derived-mate] and of the coefficient comparison.

7. Assume \(p\mathcal O_S=0\). It implies \(p\mathcal O_X=0\) by the structural map. Write
\(\sigma_T\) for the ring-sheaf map \(a\mapsto a^p\) on either small site and
\(\operatorname{Res}_{\sigma_T}\) for [def-pc-sheaf-restrict-scalars]. The latter is exact,
since it leaves underlying groups, kernels and sheafified cokernels unchanged. There is an
exact-functor isomorphism \(\epsilon_T^*\operatorname{Res}_{\sigma_{T,\mathrm{Zar}}}\cong\operat
orname{Res}_{\sigma_{T,\mathrm{Et}}}\epsilon_T^*\): on affine étale
\(\operatorname{Spec}B\to\operatorname{Spec}A\) it sends \(b\otimes m\mapsto b^p\otimes m\).
Indeed, since \(\operatorname{Spec}B\to\operatorname{Spec}A\) is étale and \(p=0\) in \(A\),
[lem-fd-etale-relative-frobenius-iso] says that \(B\otimes_{A,F_A}A\to B\), \(b\otimes a\mapsto
b^pa\), is invertible. Tensor its inverse over the second \(A\) with the module: the source is
\(B\otimes_A\operatorname{Res}_{F_A}M\) after \((b\otimes a)\otimes m\mapsto b\otimes am\). This
proves the displayed isomorphism for every module, without perfection or Frobenius-flatness. Its
formula commutes with localization, so the sheafification model of
[lem-fd-etale-zariski-ringed-pullback-flat] glues it.

8. For either topology, direct image commutes with \(\operatorname{Res}_{\sigma}\): at each
object it is the same additive sections functor with scalars acting by their \(p\)-th powers.
The underived tensor-adjunction exchange square commutes with these restrictions and the
isomorphisms of Step 7. On a tensor generator \(b\otimes s\), the two routes are restriction of
\(b^p\otimes s\); the equality uses \((bs)^p=b^ps^p\) when the coefficient map is Frobenius.
Thus the underived cube hypothesis of [lem-weil-pbc-right-derived-plus-cube] holds, with its
four vertical functors the exact scalar restrictions and its horizontal exact functors the two
\(\epsilon^*\)'s. The coefficient-restriction comparisons for the vertical direct images are
invertible: after forgetting to abelian sheaves they are the identity comparison, by the
compatible-ring-map naturality of [lem-pur-ringed-coefficient-restriction-counit]. The cube node
gives the cube equality for the chosen bounded-below derived exchange maps (their normalization
is [lem-fd-flat-ringed-square-derived-mate]). Apply its naturality to the linear arrow
\(\mathcal O_X\to\operatorname{Res}_{\sigma_X}\mathcal O_X\), \(s\mapsto s^p\). After forgetting
scalars, this is precisely additive Frobenius on both sides of Step 6; the
coefficient-restriction comparison is natural in compatible ring-sheaf homomorphisms by
[lem-pur-ringed-coefficient-restriction-counit]. Hence the isomorphism intertwines Frobenius in
the derived category. The target of the linear Frobenius arrow has scalar action \(a\cdot
e=a^pe\), so on cohomology it gives \(F(ae)=a^pF(e)\); exact pullback commutes with cohomology
by [lem-weil-pbc-exact-functor-bounded-below].
-/
theorem relativeEtaleZariskiDerivedComparison
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ∃ c : RelativeEtaleZariskiContext f,
      IsIso (c.arrow F) ∧
      (∀ (G : X.Modules) [G.IsQuasicoherent] (g : F ⟶ G),
        c.targetDerived.map ((pushforward f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g)) ≫ c.arrow G =
        c.arrow F ≫ (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).map
            ((c.source.extension ⋙ relativeEtaleForgetModules X).map g))) ∧
      (∀ (p : ℕ), p.Prime → (p : S.ringCatSheaf.obj.obj (op ⊤)) = 0 →
        F = SheafOfModules.unit X.ringCatSheaf →
        ∃ t : RelativeEtaleZariskiFrobeniusSquare c p,
          t.sourceAction ≫ c.arrow (SheafOfModules.unit X.ringCatSheaf) =
            c.arrow (SheafOfModules.unit X.ringCatSheaf) ≫ t.targetAction ∧
          ∀ (q : ℕ) (V : S.Etale) (a : (smallEtaleModuleRing S).obj.obj (op V))
            (e : (c.target.extension.obj
              (((pushforward f).rightDerived q).obj
                (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)),
            t.sectionAction q V (a • e) = a ^ p • t.sectionAction q V e) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
