/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIdentify
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
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
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The complex representative of the flat scalar push mate

Source: the current blueprint, rational proper base change, paragraph (1), canonical scalar
comparison before continuity; the explicit eight-step normalization recorded in the DAG
(blueprint: lem-sfb-flat-scalar-push-resolution-formula).

We use internal module objects, as allowed by the statement. Restricting the ordinary mate
and then applying the ordinary restriction/direct-image comparison gives `flatScalarPushMap`.
The theorem is an equality in the derived category. Its units and counits display all the
canonical identifications, including the target identification induced by the prescribed
resolution. No action of the larger coefficient ring on the target resolution is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- Termwise scalar tensor, retaining only the original coefficient action.
Source: the scalar tensor in the complex-representative statement, paragraph (1) of the
rational proper-base-change proof (blueprint: lem-sfb-flat-scalar-push-resolution-formula).
This is the existing extension followed by restriction, applied degreewise. -/
def flatScalarComplex (Z : Scheme.{u}) :
    CochainComplex (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) ℤ ⥤
      CochainComplex (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) ℤ :=
  (Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ) ⋙
    (Mod.comap (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)

/-- The map `m_{S,C}` is restriction of the termwise ordinary push mate. On local pure tensors
it sends `s ⊗ c` to `p^#(s) ⊗ c`; this is a local formula before sheafification, not a claim
about global sections of tensor sheaves. The last factor is the ordinary identification of
restriction with direct image.
Source: rational proper-base-change proof, paragraph (1), and the DAG's step 3
(blueprint: lem-sfb-flat-scalar-push-resolution-formula). -/
def flatScalarPushMap {X Y : Scheme.{u}} (p : X ⟶ Y)
    (C : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)) ℤ) :
    (flatScalarComplex a Y).obj (((lowerStar R p).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar R p).mapHomologicalComplex (.up ℤ)).obj ((flatScalarComplex a X).obj C) :=
  ((Mod.comap (coefficientMap a Y)).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pushHom a p) (.up ℤ)).app C) ≫
    (NatTrans.mapHomologicalComplex (comapLowerStarIso a p).hom (.up ℤ)).app
      (((Mod.extendScalars (coefficientMap a X)).mapHomologicalComplex (.up ℤ)).obj C)

variable [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

/-- The flat scalar push mate has the specified complex representative for every K-injective
complex `C` and every prescribed quasi-isomorphism `h` to an R-linear K-injective `J`.
The left side first changes the source by the right-derived unit at `C`, applies the
restricted derived mate and canonical direct-image comparison, and changes the target by
`h`. The right side is the localization of `m_{S,C}` followed by `p_*(h)`, with the source
flat-scalar counit and the right-derived unit at `J`. Those comparisons are invertible:
flatness makes the scalar counits invertible on all complexes, and K-injectivity makes the
two right-derived units invertible. Thus this equation specifies exactly the representative,
including its resolution-induced target identification.

Here `derivedComapLowerStarIso` is the internal-module coordinate of the canonical `d`;
the exact section-module equivalences and their unit-normalized comparisons identify it
with the ring-sheaf comparison in the statement.

Source: rational proper-base-change proof, paragraph (1), canonical comparison before
continuity; the agent calculation in the node
(blueprint: lem-sfb-flat-scalar-push-resolution-formula).

Proof plan, following the node's eight steps:
1. Transport through the exact section-module equivalences and their pure-tensor
   comparisons if desired. Exact extension and restriction derive termwise; the flat
   scalar comparison is the existing left-derived counit on every complex.
2. The ordinary extension/restriction adjunction descends through localization. Its unit
   is `c ↦ 1 ⊗ c` and its counit is multiplication, fixing the derived adjunction itself.
3. Expand the ordinary mate: its local formula is `s ⊗ c ↦ p^#(s) ⊗ c`. Local generators
   determine the sheaf map and naturality gives a map of complexes, `flatScalarPushMap`.
4. Choose an S-linear K-injective resolution `k` of the tensor complex. Restriction
   preserves K-injectives because its left adjoint is exact. Direct image also preserves
   them because module pullback is exact; restriction on Y does so for the same reason.
5. Compute the canonical restriction/direct-image comparison using `k`. Composition of
   right-derived functors gives the localization of `comapLowerStarIso`, through the units.
6. Expand `derivedPushHom` as the scalar mate of that comparison. The adjunction unit
   and the right-derived unit give the map `c ↦ k(1 ⊗ c)` on the chosen resolutions.
7. Transpose by scalar adjunction: the map is `s ⊗ c ↦ k(p^#(s) ⊗ c)`. Its restriction
   is `p_*(Res k)` after `flatScalarPushMap`, with the same source and target comparisons.
8. Compare `Res k` with the prescribed `h` by the Hom bijection into K-injectives. The
   unique homotopy class `q` satisfies `q (Res k) ≃ h`; direct image preserves this
   homotopy. Naturality of the right-derived unit gives precisely the target change by
   `h` below. This works for arbitrary unbounded complexes, without a claim of invertibility
   for the mate. -/
theorem flatScalarPushResolutionFormula {X Y : Scheme.{u}} (p : X ⟶ Y)
    (C J : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)) ℤ)
    [C.IsKInjective] [J.IsKInjective]
    (h : (flatScalarComplex a X).obj C ⟶ J) [QuasiIso h] :
    (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.map
            ((lowerStar R p).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
          (derivedPushHom a p).app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) ≫
      (derivedComapLowerStarIso a p).hom.app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) ≫
      (moduleObjectDerivedPushforward R p).map
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.map
            ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
          (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
            (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map h)) =
    (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app
          (((lowerStar R p).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) ≫
      (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj
          (((lowerStar R p).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        (flatScalarPushMap a p C ≫ ((lowerStar R p).mapHomologicalComplex (.up ℤ)).map h)) ≫
      (lowerStar R p).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj J) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
