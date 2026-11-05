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

/-! # Integral normalization of a finite étale lift -/
@[expose] public noncomputable section
set_option autoImplicit false
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
private theorem restrictionInverseSection (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj M).val.obj U) :
    HEq (((restrictionUnderlying l T r n).inv.app M).hom.app U x) x := by
  change HEq ((eqToHom (r.underlying M n U).symm) x) x
  exact finiteBoundary_cast_heq _ _
set_option maxHeartbeats 1000000 in
-- Converting the three concrete sheaf module presentations requires extra reduction.
private theorem rootEndpoint (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n) :
    finiteRootMap l (ULift.{u} (Padic l)) (diagonalSurface Y) n ≫
      (finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n).map
        (lineEvaluation l (ULift.{u} (Padic l)) c n).inv ≫
      (evalIso l (diagonalSurface Y) r n).inv.app
        (lineModule l (ULift.{u} (Padic l)) c) ≫
      (diagonalForget l (diagonalSurface Y)).map a.line.hom ≫
      (diagonalFiniteForgetIso l n (diagonalSurface Y)).inv.app
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)) =
        cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n) := by
  have hr := finiteBoundary_rootMap l (ULift.{u} (Padic l)) c n
  rw [← hr]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
  have hline := diagonalFiniteForgetIso_transport l n (diagonalSurface Y)
    ((diagonalForget l (diagonalSurface Y)).obj
      ((r.F.obj (lineModule l (ULift.{u} (Padic l)) c)).obj (op n)))
    (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
    ((diagonalForget l (diagonalSurface Y)).map a.line.hom)
    (k.lineForget.hom.app (op n) ≫
      cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
        (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n))
    a.line_roots
  rw [hline]
  apply Sheaf.hom_ext
  ext U z
  let T := diagonalSurface Y
  let x' := (c.rootForget.inv.app (op n)).hom.app U z
  let x : c.rootModule.val.obj (op (n, U.unop)) :=
    (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
  have hx : HEq x' x := (finiteBoundary_cast_heq
    (c.reduction.forget.sections c.rootModule n U) x').symm
  let η := c.scalar.ordinaryAdjunction.unit.app c.rootModule
  have hf := finiteBoundary_forgetMapSection T _ c.reduction.forget η n U x x' hx
  have he := finiteScalarForgetIso_section l (ULift.{u} (Padic l)) c n
    (lineModule l (ULift.{u} (Padic l)) c) U _ _ hf
  have hu : η.val.app (op (n, U.unop)) x =
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)
        c.scalar c.rootModule (op (n, U.unop)) x :=
    scalarUnitSection.{u + 1, u, u + 1} _ c.scalar c.rootModule _ x
  let v := ((finiteScalarForgetIso l (ULift.{u} (Padic l)) c n).hom.app
    (lineModule l (ULift.{u} (Padic l)) c)).hom.app U
      (((c.reduction.forget.F.map η).app (op n)).hom.app U x')
  let w := ((evalIso l T r n).inv.app
    (lineModule l (ULift.{u} (Padic l)) c)).hom.app U v
  have hw : HEq w v := restrictionInverseSection l T r n _ U v
  have ht := k.line_tensor n U x x' w hx.symm
    (hw.trans ((heq_of_eq he).trans (heq_of_eq hu)))
  have hi := congrArg (fun f ↦ f.hom.app U z) (c.rootForget.app (op n)).inv_hom_id
  change (c.rootForget.hom.app (op n)).hom.app U x' = z at hi
  change ((cartierProRootMap _ _ _ _ _ _).hom.app U)
    ((k.lineForget.hom.app (op n)).hom.app U w) = _
  rw [ht, hi]
  rfl

section IntegralBoundaryCalculation

attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] CategoryTheory.constantSheaf comparisonLowerStar
  Functor.sheafPushforwardContinuous Scheme.toProEt

private theorem moduleForget_apply (A : Type (u + 1)) [CommRing A]
    {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (x : M) :
    ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map f) x = f x := by
  rfl

set_option maxHeartbeats 1000000 in
-- Compare the terminal generators in the two sheafification presentations.
private theorem integerComparisonGenerator (T : Scheme.{u}) (x : ULift.{u + 1} ℤ) :
    ((integerComparison T).hom.hom.app (op (Scheme.ProEt.mk (𝟙 T))))
      ((((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).hom.app (op (Scheme.Etale.mk (𝟙 T))))
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                (op (Scheme.Etale.mk (𝟙 T))) x)) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (Scheme.ProEt.mk (𝟙 T))) x := by
  let adj1 := (((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId T)).comp
      (comparisonAdjunction AddCommGrpCat.{u + 1} T)).ofNatIsoRight
        ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
          AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
            (op (Scheme.Etale.mk (𝟙 T)))))
  let adj2 := constantSheafAdj (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId T)
  have hh := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hh' := ConcreteCategory.congr_hom hh x
  change ((integerComparison T).hom.hom.app (op (Scheme.ProEt.mk (𝟙 T)))) _ = _ at hh'
  exact hh'

private theorem forgetComparison_unit (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        ((Etale.RawModuleScalarComparison.forget A T).obj M) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} T).map
        ((forgetComparisonIso A T).hom.app M) =
      (Etale.RawModuleScalarComparison.forget A T).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M) := by
  rw [forgetComparisonIso_hom]
  let e := (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv
    ((Etale.RawModuleScalarComparison.forget A T).obj M)
    ((cartierForget A T).obj ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M))
  exact e.apply_symm_apply _

private theorem constantAb_ext_one (T : Scheme.{u}) (M : DiagonalAb T)
    (f g : (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ M)
    (h : f.hom.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1)) =
      g.hom.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1))) : f = g := by
  apply ((constantSheafAdj (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId T)).homEquiv _ _).injective
  apply (M.obj.obj (op (Scheme.ProEt.mk (𝟙 T)))).uliftZMultiplesAddEquiv.injective
  simp only [AddCommGrpCat.uliftZMultiplesAddEquiv_eq, constantSheafAdj_homEquiv_eq]
  exact h

private theorem ordinaryIntegralGenerator_section (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (x : ULift.{u + 1} ℤ) :
    (Etale.ordinaryFiniteIntegralGenerator A T).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (Scheme.Etale.mk (𝟙 T))) x) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.Etale.mk (𝟙 T))) (x.down : A) := by
  have h := ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId T)).homEquiv
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
      ((Etale.moduleAbelianForget A T).obj (Etale.ordinaryFiniteConstant A T))).apply_symm_apply
      (AddCommGrpCat.ofHom
        ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
              (op (Scheme.Etale.mk (𝟙 T))))).hom).comp
          ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)))
  rw [constantSheafAdj_homEquiv_eq] at h
  exact ConcreteCategory.congr_hom h x

private def siteIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
        (cartierForget A T).obj (geoCartierConstant A T) :=
  (integerComparison T).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
      (Etale.ordinaryFiniteIntegralGenerator A T) ≫
    (forgetComparisonIso A T).hom.app (Etale.ordinaryFiniteConstant A T) ≫
    (cartierForget A T).map (finiteEtaleConstantIso A T).hom

set_option maxHeartbeats 1000000 in
-- Compare the terminal generators in the two sheafification presentations.
private theorem siteIntegralGenerator_section (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (x : ULift.{u + 1} ℤ) :
    (siteIntegralGenerator A T).hom.app (op (Scheme.ProEt.mk (𝟙 T)))
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (Scheme.ProEt.mk (𝟙 T))) x) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.ProEt.mk (𝟙 T))) (x.down : A) := by
  rw [← integerComparisonGenerator T x]
  change (((integerComparison T).hom ≫ siteIntegralGenerator A T).hom.app
    (op (Scheme.ProEt.mk (𝟙 T)))) _ = _
  simp only [siteIntegralGenerator, Iso.hom_inv_id_assoc]
  have hn := (comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.naturality
    (Etale.ordinaryFiniteIntegralGenerator A T)
  have hf := forgetComparison_unit A T (Etale.ordinaryFiniteConstant A T)
  have hg := ordinaryIntegralGenerator_section A T x
  have hc := comparison_constant_generator A T (x.down : A)
  -- The following calculation only evaluates the naturality and unit equations.
  have hn' := congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (Scheme.Etale.mk (𝟙 T))) x)) hn
  have hf' := congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
        (op (Scheme.Etale.mk (𝟙 T))) (x.down : A))) hf
  simp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hn' hf'
  change ((finiteEtaleConstantIso A T).hom.hom.app _)
    (((forgetComparisonIso A T).hom.app _).hom.app _
      (((comparisonUpperStar AddCommGrpCat.{u + 1} T).map
        (Etale.ordinaryFiniteIntegralGenerator A T)).hom.app _ _)) = _
  erw [← hn', hg, hf']
  unfold finiteEtaleConstantIso geoCartierConstant
  simp only [Etale.RawModuleScalarComparison.forget, Etale.moduleAbelianForget,
    sheafCompose_map_hom, Functor.whiskerRight_app]
  erw [moduleForget_apply]
  exact hc

set_option maxHeartbeats 1000000 in
-- Match the concrete evaluation and scalar-restriction module presentations.
private theorem sourceEndpoint (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n) :
    finiteQuotient l (ULift.{u} (Padic l)) (diagonalSurface Y) n ≫
      (evalIso l (diagonalSurface Y) r n).inv.app
        (coefficient (diagonalSurface Y) (Arings l (ULift.{u} (Padic l))
          (diagonalSurface Y))) ≫
      (diagonalForget l (diagonalSurface Y)).map a.coefficient.hom ≫
      (diagonalFiniteForgetIso l n (diagonalSurface Y)).inv.app
        (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y)) =
      siteIntegralGenerator (diagonalResidue.{u} l n) (diagonalSurface Y) := by
  apply constantAb_ext_one
  let T := diagonalSurface Y
  let U := op (Scheme.ProEt.mk (𝟙 T))
  let z := (toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
      (ULift.up 1)
  let x' := (finiteQuotient l (ULift.{u} (Padic l)) T n).hom.app U z
  let x := ((evalIso l T r n).inv.app
    (coefficient T (Arings l (ULift.{u} (Padic l)) T))).hom.app U x'
  have hq := (finiteQuotient_existsUnique l (ULift.{u} (Padic l)) T n).exists.choose_spec
      U (ULift.up 1)
  have hx' : HEq x' (1 : (systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop))) := by
    simpa only [x', z, finiteQuotient, Int.cast_one] using hq
  have hx : HEq x x' := restrictionInverseSection l T r n _ U x'
  have ha := a.coefficient_one U x (hx.trans hx')
  have hi (y : ((diagonalForget l T).obj ((diagonalFiniteToPadic l n T).obj
      (geoCartierConstant (diagonalResidue.{u} l n) T))).obj.obj U) :
      HEq (((diagonalFiniteForgetIso l n T).inv.app
        (geoCartierConstant (diagonalResidue.{u} l n) T)).hom.app U y) y := by
    unfold diagonalFiniteForgetIso diagonalFiniteToPadic diagonalForget cartierForget
    rfl
  have ht := (hi (a.coefficient.hom.hom.app U x)).trans ha
  have hs := siteIntegralGenerator_section (diagonalResidue.{u} l n) T (ULift.up 1)
  change (((diagonalFiniteForgetIso l n T).inv.app
      (geoCartierConstant (diagonalResidue.{u} l n) T)).hom.app U)
    (a.coefficient.hom.hom.app U x) = (siteIntegralGenerator _ T).hom.app U z
  rw [hs]
  simpa only [Int.cast_one] using eq_of_heq ht

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

private theorem integralImage (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (b : Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2) :
    (Ext.mk₀ (siteIntegralGenerator A T)).comp
      ((finiteEtaleProImage A T N hA b).mapExactFunctor (cartierForget A T))
      (zero_add 2) =
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison T).inv
      ((Etale.ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
        (Etale.ordinaryFiniteExtHomEquiv A T _ _ 2 b)).mapExactFunctor
          (comparisonUpperStar AddCommGrpCat.{u + 1} T))
      ((forgetComparisonIso A T).hom.app (Scheme.finiteEtaleTateLine T N A hA)) := by
  have hn := Ext.mapExactFunctor_square
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (Etale.RawModuleScalarComparison.forget A T) (cartierForget A T)
    (forgetComparisonIso A T) b
  rw [Etale.ordinaryFiniteClass_extHomEquiv]
  simp only [Etale.ordinaryFiniteExtClassCore, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀CompMk₀]
  rw [finiteEtaleProImage_apply, Ext.mapExactFunctor_mk₀CompMk₀]
  unfold siteIntegralGenerator
  rw [Ext.mk₀_comp_mk₀CompMk₀]
  simp only [Category.assoc, ← (cartierForget A T).map_comp,
    Iso.hom_inv_id, (cartierForget A T).map_id]
  simp only [Ext.mk₀CompMk₀, finiteEtaleLineIso, Iso.refl_hom,
    (cartierForget A T).map_id, Ext.comp_mk₀_id]
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc]
  erw [Ext.mk₀_id_comp, ← hn]

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

set_option maxHeartbeats 1000000 in
-- Realizing the tower extension traverses both derived-category presentations.
private theorem evaluatedIntegralKummerClass_hom
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0) (k : Kummer l T)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (P : T.Pic) :
    (evaluatedIntegralKummerClass l T A n hA k hN P).hom =
      evaluatedTowerBoundary l T n k P ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧' := by
  unfold evaluatedIntegralKummerClass evaluatedTowerBoundary
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext]
  have hi : (Ext.homEquiv.symm (lineBundleClass T P) :
      Ext.{u + 2} (integers T) (units T) 1).hom = lineBundleClass T P :=
    Ext.homEquiv.apply_symm_apply _
  rw [kummerComposite_hom, hi]
  rfl

set_option maxHeartbeats 1000000 in
-- Combining the large coefficient presentations requires extra elaboration.

/-- The integral adjunct of a supplied lift is the evaluated tower Kummer composite.
The right side uses only the tower extension and the pro-etale root map; it makes
no assertion identifying that composite with an etale cohomology class.

Source: geometric tower classes proof (2), finite scalar-unit square and evaluation;
diagonal trace proof (2), coefficient-one and root-tensor coordinates.
(blueprint: lem-sfb-diagonal-trace-finite-etale-integral-boundary).

Proof: apply hc to P,n and remove its HEq witnesses. Forget hb to abelian sheaves
using forgottenFiniteEquation. The natural isomorphism evalIso identifies the
underlying restricted functor with intrinsic finite evaluation. Transport the
coefficient source through this isomorphism and the frame. On constant one,
finiteQuotient, restrictionInverseSection and a.coefficient_one show that it
is the site-comparison integral generator. The constant-sheaf adjunction and
additivity extend this equality to all sections. At the target use rootEndpoint,
whose proved section calculation uses the scalar unit and k.line_tensor.
Naturality of exact single-arrow transport now pastes the two endpoint squares
with the finite boundary equality. Ext.homEquiv is injective, so the resulting
hom identity is the stated Ext identity. Ext.mapExactFunctor and the natural
forgetComparisonIso move ordinary coefficient forgetting past site comparison.
This argument does not compare the tower Kummer extension with the etale one,
and never cancels arbitrary derived scalar restriction. -/
theorem diagonalTrace_finiteEtale_integralBoundary
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (P : (diagonalSurface Y).Pic)
    (b : Ext (Etale.ordinaryFiniteConstant (diagonalResidue.{u} l n)
      (diagonalSurface Y)) (Scheme.finiteEtaleTateLine (diagonalSurface Y)
        (l ^ (n + 1)) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))) 2)
    (hb : finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
      a.coefficient a.line (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P)
      (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y)
        (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) b)) :
    Ext.mk₀CompMk₀ (integerComparison (diagonalSurface Y)).inv
      ((Etale.ordinaryFiniteClass (diagonalResidue l n) (diagonalSurface Y)
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) (l ^ (n + 1))
          (diagonalResidue l n) (cartierResidue_cast l (n + 1))) 2
        (Etale.ordinaryFiniteExtHomEquiv (diagonalResidue l n) (diagonalSurface Y)
          _ _ 2 b)).mapExactFunctor
            (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)))
      ((forgetComparisonIso (diagonalResidue l n) (diagonalSurface Y)).hom.app
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) (l ^ (n + 1))
          (diagonalResidue l n) (cartierResidue_cast l (n + 1)))) =
    evaluatedIntegralKummerClass l (diagonalSurface Y) (diagonalResidue l n) n
      (cartierResidue_cast l (n + 1)) c.kummer
      (diagonalSurface_power_unit l Y hY n) P := by
  let T := diagonalSurface Y
  let E := ULift.{u} (Padic l)
  let A := diagonalResidue.{u} l n
  let S := DerivedCategory.singleFunctor.{u + 1} (DiagonalAb T) 0
  let M := coefficient T (Arings l E T)
  let L := lineModule l E c
  let y := finiteEtaleProImage A T (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) b
  let f := firstChern l E c P
  let β := evaluatedTowerBoundary l T n c.kummer P
  have hb' := forgottenFiniteEquation r.F (diagonalFiniteToPadic l n T)
    (diagonalForget l T) n a.coefficient a.line f y hb
  have hE := mapSingleArrow_natIso _ _ (evalIso l T r n).symm (2 : ℤ) f
  have hd := mapSingleArrow_natIso _ _ (diagonalFiniteForgetIso l n T) (2 : ℤ) y.hom
  obtain ⟨α, β', hα, hβ, hN⟩ := hc P n
  have hα' := eq_of_heq hα
  have hβ' := eq_of_heq hβ
  rw [hα', hβ'] at hN
  simp only [evaluatedChern, mapSingleArrow_postcompose,
    mapSingleArrow_composite] at hN
  have hh := normalizedLift_glue
    (S.map (finiteQuotient l E T n)) β (S.map (finiteRootMap l E T n))
    (S.mapIso ((evalIso l T r n).app M)) (S.mapIso ((evalIso l T r n).app L))
    (S.mapIso ((diagonalForget l T).mapIso a.coefficient))
    (S.mapIso ((diagonalForget l T).mapIso a.line))
    (S.mapIso ((diagonalFiniteForgetIso l n T).app (geoCartierConstant A T)))
    (S.mapIso ((diagonalFiniteForgetIso l n T).app (geoCartierLine A (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) T)))
    (S.mapIso ((finiteForget l E T n).mapIso (lineEvaluation l E c n)))
    (mapSingleArrow (SpTowerShriek.ev l E T n ⋙ finiteForget l E T n) (2 : ℤ) f)
    (mapSingleArrow (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
      diagonalForget l T) (2 : ℤ) f)
    (mapSingleArrow (diagonalFiniteToPadic l n T ⋙ diagonalForget l T) (2 : ℤ) y.hom)
    (mapSingleArrow (cartierForget A T) (2 : ℤ) y.hom) hN hE hb' hd
  rw [← integralImage]
  apply Ext.ext.{u + 1}
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext,
    evaluatedIntegralKummerClass_hom]
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv,
    ← S.map_comp] at hh
  erw [sourceEndpoint l Y hY c r k n a, rootEndpoint l Y hY c r k n a] at hh
  exact hh

end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace
