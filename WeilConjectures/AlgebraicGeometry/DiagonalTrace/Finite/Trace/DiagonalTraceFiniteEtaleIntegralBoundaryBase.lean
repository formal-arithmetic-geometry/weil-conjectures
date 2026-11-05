/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerClass
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

/-! # Shared constructions for the integral boundary of a finite étale lift -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  comparisonUpperStar diagonalFiniteToPadic diagonalForget SpTowerClasses.lineModule

open SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem forgottenFiniteEquation
    {C B D H : Type*} [Category C] [Category B] [Category D] [Category H]
    [Abelian C] [Abelian B] [Abelian D] [Abelian H]
    [HasExt B] [HasExt D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    [HasDerivedCategory H] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ (ℕᵒᵖ ⥤ D)) (S : B ⥤ D) (V : D ⥤ H)
    [F.Additive] [S.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {X Y : C} {P Q : B} (n : ℕ)
    (a : (F.obj X).obj (op n) ≅ S.obj P)
    (b : (F.obj Y).obj (op n) ≅ S.obj Q)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (y : Ext P Q 2) (hy : finiteEvaluationEquation F S n a b f y) :
    mapSingleArrow (S ⋙ V) (2 : ℤ) y.hom =
      (DerivedCategory.singleFunctor H 0).map (V.map a.inv) ≫
        mapSingleArrow ((F ⋙ (evaluation ℕᵒᵖ D).obj (op n)) ⋙ V) (2 : ℤ) f ≫
          ((DerivedCategory.singleFunctor H 0).map (V.map b.hom))⟦(2 : ℤ)⟧' := by
  have h : mapSingleArrow S (2 : ℤ) y.hom =
      (DerivedCategory.singleFunctor D 0).map a.inv ≫
        mapSingleArrow (F ⋙ (evaluation ℕᵒᵖ D).obj (op n)) (2 : ℤ) f ≫
          ((DerivedCategory.singleFunctor D 0).map b.hom)⟦(2 : ℤ)⟧' := by
    unfold finiteEvaluationEquation at hy
    rw [← mapSingleArrow_composite]
    simp only [Ext.mapExactFunctor_hom, ShiftedHom.map, mapSingleArrow,
      supportedFiniteSingleCoordinates, supportedFiniteShiftedCoordinates,
      Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, Nat.cast_ofNat] at hy ⊢
    erw [Functor.commShiftIso_hom_naturality_assoc]
    exact hy
  have hh := congrArg (mapSingleArrow V (2 : ℤ)) h
  simpa only [mapSingleArrow_composite, mapSingleArrow_postcompose,
    mapSingleArrow_precompose] using hh

private def evalIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) :
    r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T ≅
      SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
        finiteForget l (ULift.{u} (Padic l)) T n :=
  restrictionUnderlying l T r n

open WeilConjectures
attribute [local implicit_reducible] spCoefficientCommRings
  SpTowerShriek.tau Functor.ofOpSequence Functor.ofSequence
  SemilinearSections.evaluation
attribute [local irreducible] SemilinearSections.scalarExtensionSection
  cartierProRootMap

attribute [local semireducible] diagonalForget SpTowerClasses.lineModule

section IntegralBoundaryCalculation

attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] CategoryTheory.constantSheaf comparisonLowerStar
  Functor.sheafPushforwardContinuous Scheme.toProEt

private def siteIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
        (cartierForget A T).obj (geoCartierConstant A T) :=
  (integerComparison T).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
      (Etale.ordinaryFiniteIntegralGenerator A T) ≫
    (forgetComparisonIso A T).hom.app (Etale.ordinaryFiniteConstant A T) ≫
    (cartierForget A T).map (finiteEtaleConstantIso A T).hom

private theorem normalizedLift_glue {D : Type*} [Category D] [HasShift D ℤ]
    {I K X Y R S A B A₀ B₀ L : D}
    (q : I ⟶ X) (f : I ⟶ K⟦(2 : ℤ)⟧) (r : K ⟶ L)
    (eX : R ≅ X) (eY : S ≅ Y) (aX : R ≅ A) (aY : S ≅ B)
    (dX : A₀ ≅ A) (dY : B₀ ≅ B) (s : Y ≅ L)
    (fX : X ⟶ Y⟦(2 : ℤ)⟧) (fR : R ⟶ S⟦(2 : ℤ)⟧)
    (y : A ⟶ B⟦(2 : ℤ)⟧) (y₀ : A₀ ⟶ B₀⟦(2 : ℤ)⟧)
    (hN : q ≫ fX ≫ s.hom⟦(2 : ℤ)⟧' = f ≫ r⟦(2 : ℤ)⟧')
    (hE : eX.inv ≫ fR = fX ≫ eY.inv⟦(2 : ℤ)⟧')
    (hb : y = aX.inv ≫ fR ≫ aY.hom⟦(2 : ℤ)⟧')
    (hd : dX.hom ≫ y = y₀ ≫ dY.hom⟦(2 : ℤ)⟧') :
    (q ≫ eX.inv ≫ aX.hom ≫ dX.inv) ≫ y₀ =
      f ≫ (r ≫ s.inv ≫ eY.inv ≫ aY.hom ≫ dY.inv)⟦(2 : ℤ)⟧' := by
  have hy : y₀ = dX.hom ≫ y ≫ dY.inv⟦(2 : ℤ)⟧' := by
    rw [← Category.assoc, hd]
    simp only [Category.assoc, ← (shiftFunctor D (2 : ℤ)).map_comp,
      dY.hom_inv_id, (shiftFunctor D (2 : ℤ)).map_id, Category.comp_id]
  rw [hy, hb]
  simp only [Category.assoc, dX.inv_hom_id_assoc, aX.hom_inv_id_assoc]
  rw [reassoc_of% hE]
  have hn : q ≫ fX = f ≫ (r ≫ s.inv)⟦(2 : ℤ)⟧' := by
    have hh := congrArg (fun a ↦ a ≫ s.inv⟦(2 : ℤ)⟧') hN
    simpa only [Category.assoc, ← (shiftFunctor D (2 : ℤ)).map_comp,
      s.hom_inv_id, (shiftFunctor D (2 : ℤ)).map_id, Category.comp_id] using hh
  rw [← Category.assoc q fX, hn]
  simp only [Functor.map_comp, Category.assoc]

attribute [local irreducible] Ext.comp Ext.mk₀ Ext.mk₀CompMk₀
  Ext.mapExactFunctor Ext.homEquiv diagonalForget SpTowerClasses.lineModule
attribute [local implicit_reducible] geoCartierLine

-- Use the same intrinsic abelian-sheaf localization as FiniteChernNormalization.
@[instance_reducible] private def integralAbDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (DiagonalAb T) := inferInstance
attribute [local instance 100000] integralAbDerived

private theorem kummerComposite_hom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasExt C]
    (s : ShortComplex C) (hs : s.ShortExact) {X : C} (β : Ext X s.X₃ 1) :
    (β.comp hs.extClass (rfl : 1 + 1 = 2)).hom = kummerComposite s hs β.hom := by
  simp only [kummerComposite, Ext.comp_hom, hs.extClass_hom, ShiftedHom.comp,
    Int.natCast_add, Int.natCast_one, shiftFunctorAdd'_eq_shiftFunctorAdd]

private def evaluatedTowerBoundary
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (k : Kummer l T) (P : T.Pic) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
        ((abEvaluation T n).obj (roots l T)))⟦(2 : ℤ)⟧ :=
  mapSingleArrow (abEvaluation T n) (2 : ℤ)
    (kummerComposite (C := Ab T) (ShortComplex.mk k.inclusion k.power k.zero) k.exact
      (lineBundleClass T P))

end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace
