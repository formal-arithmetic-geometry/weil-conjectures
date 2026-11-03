/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeLocalTrace
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Degree-zero unit form of local vector integration base change

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-integration-base-change-local-unit).

The remaining local exchange calculation is recorded after postcomposition with the
constant-unit pullback.  This is the degree-zero form used before cancelling that
invertible comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The local vector integration base-change equation after the constant-unit comparison.

Proof: restrict the two supplied frames along `a` and `g`, paste the Cartesian exchange
square defining `b` with the coefficient comparison `c`, and use the affine counit
base-change equation over `W`.  The two supplied frame equations replace the restricted
arbitrary arrows by the two affine local traces.  Naturality of the ordinary constant-unit
pullback then gives the displayed equation.  This is the degree-zero calculation; the
unadjusted equation follows by cancelling the final unit comparison.  Empty schemes,
rank zero, and the zero coefficient ring use the same unit equations.
(blueprint: lem-pur-vector-integration-base-change-local-unit). -/
theorem vectorIntegration_baseChange_local_unit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.baseChange f r F)).obj
        (vectorIntegrationCoefficient A N hA S r F) ≅
      vectorIntegrationCoefficient A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.baseChange f r F) (VectorBundleZeroSection.π S r F)).symm.app _ ≪≫
      (eqToIso (congrArg (ordinaryFinitePullback A)
        (VectorTraceGeometry.baseChange_isPullback f r F).w)).app _ ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F)) f).app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS r))
    (b : (ordinaryFinitePullback A f).obj (vectorIntegrationSource A N hA S r F) ≅
      vectorIntegrationSource A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.baseChange_isPullback f r F)).app
        (vectorIntegrationCoefficient A N hA S r F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).map c.hom)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (V : S.Opens) (eS : VectorBundleZeroSection.Trivialization S r F V)
    (U : T.Opens)
    (eT : VectorBundleZeroSection.Trivialization T r
      ((Scheme.Modules.tensorPullback f).obj F) U)
    (W : Scheme.{u}) [IsNoetherian W]
    (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι)
    (kS : vectorIntegrationSource A N hA S r F ⟶ ordinaryFiniteUnit A S)
    (kT : vectorIntegrationSource A N hA T r ((Scheme.Modules.tensorPullback f).obj F) ⟶
      ordinaryFiniteUnit A T)
    (hkS : (ordinaryFinitePullback A V.ι).map kS ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS r F V eS)
    (hkT : (ordinaryFinitePullback A U.ι).map kT ≫ (ordinaryFiniteUnitPullback A U.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D T (affineTracePullbackInvertible N f hS) r
        ((Scheme.Modules.tensorPullback f).obj F) U eT) :
    (ordinaryFinitePullback A j).map (b.hom ≫ kT) ≫
        (ordinaryFiniteUnitPullback A j).hom =
      (ordinaryFinitePullback A j).map
        ((ordinaryFinitePullback A f).map kS ≫ (ordinaryFiniteUnitPullback A f).hom) ≫
        (ordinaryFiniteUnitPullback A j).hom := by
  have hcore := vectorIntegration_baseChange_local_trace N hN A hA t f hS r F c hc b hb D
    V eS U eT W j a g ha hg
  have hunitT := ordinaryFiniteUnitPullback_comp A a U.ι j ha.symm
  have hnatT :=
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.naturality kT
  simp only [Functor.comp_map] at hnatT
  have hnatS :=
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.naturality kS
  simp only [Functor.comp_map] at hnatS
  have hnatJF :=
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).hom.naturality kS
  simp only [Functor.comp_map] at hnatJF
  have hunitJF := ordinaryFiniteUnitPullback_comp A j f (g ≫ V.ι) hg.symm
  have hunitGV := ordinaryFiniteUnitPullback_comp A g V.ι (g ≫ V.ι) rfl
  have hright :
      (ordinaryFinitePullback A j).map
          ((ordinaryFinitePullback A f).map kS ≫
            (ordinaryFiniteUnitPullback A f).hom) ≫
          (ordinaryFiniteUnitPullback A j).hom =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.app _ ≫
          (ordinaryFinitePullback A g).map
            ((ordinaryFinitePullback A V.ι).map kS ≫
              (ordinaryFiniteUnitPullback A V.ι).hom) ≫
          (ordinaryFiniteUnitPullback A g).hom := by
    apply (cancel_epi
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).hom.app _)).mp
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
    dsimp only [ordinaryFinitePullback] at hnatJF hnatS hunitJF hunitGV ⊢
    rw [← reassoc_of% hnatJF]
    rw [hunitJF]
    rw [← hunitGV, ← reassoc_of% hnatS]
  calc
    (ordinaryFinitePullback A j).map (b.hom ≫ kT) ≫
        (ordinaryFiniteUnitPullback A j).hom =
      (ordinaryFinitePullback A j).map b.hom ≫
        (ordinaryFinitePullback A j).map kT ≫
        (ordinaryFiniteUnitPullback A j).hom := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
    _ = (ordinaryFinitePullback A j).map b.hom ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map
          ((ordinaryFinitePullback A U.ι).map kT) ≫
        (ordinaryFinitePullback A a).map
          (ordinaryFiniteUnitPullback A U.ι).hom ≫
        (ordinaryFiniteUnitPullback A a).hom := by
          rw [← hunitT]
          dsimp only [ordinaryFinitePullback] at hnatT ⊢
          rw [reassoc_of% hnatT]
    _ = (ordinaryFinitePullback A j).map b.hom ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map
          ((ordinaryFinitePullback A U.ι).map kT ≫
            (ordinaryFiniteUnitPullback A U.ι).hom) ≫
        (ordinaryFiniteUnitPullback A a).hom := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
    _ = (ordinaryFinitePullback A j).map b.hom ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map
          (vectorIntegrationLocalTrace N hN A hA t D T
            (affineTracePullbackInvertible N f hS) r
            ((Scheme.Modules.tensorPullback f).obj F) U eT) ≫
        (ordinaryFiniteUnitPullback A a).hom := by rw [hkT]
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.app _ ≫
        (ordinaryFinitePullback A g).map
          (vectorIntegrationLocalTrace N hN A hA t D S hS r F V eS) ≫
        (ordinaryFiniteUnitPullback A g).hom := hcore
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.app _ ≫
        (ordinaryFinitePullback A g).map
          ((ordinaryFinitePullback A V.ι).map kS ≫
            (ordinaryFiniteUnitPullback A V.ι).hom) ≫
        (ordinaryFiniteUnitPullback A g).hom := by rw [hkS]
    _ = (ordinaryFinitePullback A j).map
        ((ordinaryFinitePullback A f).map kS ≫
          (ordinaryFiniteUnitPullback A f).hom) ≫
        (ordinaryFiniteUnitPullback A j).hom := hright.symm

end AlgebraicGeometry.Etale
