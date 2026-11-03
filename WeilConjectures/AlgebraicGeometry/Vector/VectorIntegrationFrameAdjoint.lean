/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
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
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Frame normalization before restricting the integration adjunct to a section

Source: orientation-charts Step 4, transpose of integration normalization.
(blueprint: lem-trf-vector-integration-frame-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  rightDerivedLowerShriek rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
  affineLinearCompactComparison affineTraceCounit affineTraceProjection singleFunctorObjUnitIso

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

private theorem replace_middle_composite
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ Y : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (e : X₄ ⟶ X₅) (f : X₅ ⟶ Y) (z : X₁ ⟶ X₃) (h : b ≫ c = z) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ f = a ≫ z ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]
  rw [reassoc_of% h]

private theorem comp_transport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : h = f ≫ g) (K : DerivedCategoryModule A Z) :
    (eqToIso (congrArg (ordinaryFinitePullback A) w)).app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h w).app K := by
  subst h
  apply Iso.ext
  exact Category.id_comp _

private theorem mate_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : C ⥤ C'} {U : D ⥤ D'} (a : F ⊣ G) (b : F' ⊣ G')
    (e : TwoSquare V F F' U) (X : C) (K : D) (c : F.obj X ⟶ K) :
    V.map (a.homEquiv X K c) ≫ (mateEquiv a b e).app K =
      b.homEquiv _ _ (e.natTrans.app X ≫ U.map c) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Equiv.symm_apply_apply]
  rw [mateEquiv_counit]
  have hn := e.natTrans.naturality (a.homEquiv X K c)
  dsimp only [Functor.comp_map] at hn
  change F'.map (V.map (a.homEquiv X K c)) ≫
    e.natTrans.app (G.obj K) ≫ U.map (a.counit.app K) = _
  rw [reassoc_of% hn]
  rw [← U.map_comp]
  have hc := (a.homEquiv X K).symm_apply_apply c
  rw [Adjunction.homEquiv_counit] at hc
  rw [hc]

private theorem frame_mate_units
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : C ⥤ C'} {U : D ⥤ D'} (a : F ⊣ G) (b : F' ⊣ G')
    (E : F ⋙ U ⟶ V ⋙ F') [IsIso E]
    (B : C) {K₀ K₁ : D} {L₀ L₁ : D'} {R : C'}
    (c : F.obj B ⟶ K₀) (qS : K₀ ⟶ K₁) (unit₀ : U.obj K₀ ⟶ L₀)
    (qW : L₀ ⟶ L₁) (unit₁ : U.obj K₁ ⟶ L₁) (coef : V.obj B ⟶ R)
    (trace : F'.obj R ⟶ L₀)
    (hn : U.map c ≫ unit₀ = E.app B ≫ F'.map coef ≫ trace)
    (hs : unit₀ ≫ qW = U.map qS ≫ unit₁) :
    V.map (a.homEquiv B K₁ (c ≫ qS)) ≫
        (mateEquiv a b (TwoSquare.mk _ _ _ _ (inv E))).app K₁ ≫ G'.map unit₁ =
      coef ≫ b.homEquiv R L₁ (trace ≫ qW) := by
  have hn₁ : U.map (c ≫ qS) ≫ unit₁ =
      E.app B ≫ F'.map coef ≫ trace ≫ qW := by
    rw [U.map_comp, Category.assoc, ← hs, ← Category.assoc, hn]
    simp only [Category.assoc]
  have ht := congrArg (fun f ↦ (inv E).app B ≫ f) hn₁
  simp only [Category.assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc] at ht
  have hm := mate_naturality a b (TwoSquare.mk _ _ _ _ (inv E)) B K₁ (c ≫ qS)
  rw [reassoc_of% hm, ← b.homEquiv_naturality_right]
  rw [Category.assoc, NatIso.isIso_inv_app, ht, b.homEquiv_naturality_left]

/-- Integration normalization transposes to the affine adjunct on every bundle frame.
Source: orientation-charts Step 4; parent finite-ring section deformation proof Step 7.
(blueprint: lem-trf-vector-integration-frame-adjoint).
Proof: let Ex be compact-support exchange for this open Cartesian frame square. It is
invertible by open base change. Normalization says that pullback of integration followed
by constant-unit pullback is Ex followed by the affine coefficient comparison, compact
comparison inverse and ordered trace counit. Cancel Ex. Naturality of the adjunction Hom
equivalences transposes this equality: the transpose of inverse Ex is the exceptional
base-change map. Naturality in the coefficient unit replaces ordinary unit pullback by
the monoidal unit comparison. These agree by the constant-single unit square; the inverse
of singleFunctorObjUnitIso is identity. The remaining transpose is exactly towerAdjoint.
The coefficient square uses the projection compositor indexed by the given square
equality; its equality-transport presentation agrees by compositor coherence.
No section is involved. The same calculation works for rank zero, empty opens and A=0. -/
theorem vectorIntegration_frameAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme] (e : VectorBundleZeroSection.Trivialization S d M W) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    (ordinaryFinitePullback A (vectorIntegrationChart S d M W e)).map
        ((vectorBundlePurityAdjunction A S d M).homEquiv _ _
          (vectorBundleIntegration N hN A hA S hS d M)) ≫
      dualizingComplexBaseChangeMap A (vectorIntegrationChart_isPullback S d M W e) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (vectorIntegrationChart S d M W e) (VectorBundleZeroSection.π S d M)).inv.app
        (affineLinearBaseCoefficient A N hA S d) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (affineTraceProjection W.toScheme d)
        W.ι (vectorIntegrationChart S d M W e ≫ VectorBundleZeroSection.π S d M)
        (vectorIntegrationChart_isPullback S d M W e).w).hom.app
          (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A (affineTraceProjection W.toScheme d)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d).hom ≫
      (affineLinearCoefficientDescent A N hA t W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d).inv ≫
      CoordinateCounitArrows.towerAdjoint N hN A hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d := by
  change S.Modules at M
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  let sq := vectorIntegrationChart_isPullback S d M W e
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (affineTraceProjection W.toScheme d)
  let P := ordinaryFinitePullback A W.ι
  let B := vectorIntegrationCoefficient A N hA S d M
  let c := vectorBundleIntegration N hN A hA S hS d M
  let a := rightDerivedUpperShriekAdjunction A (VectorBundleZeroSection.π S d M)
  let b := rightDerivedUpperShriekAdjunction A (affineTraceProjection W.toScheme d)
  let E := rightDerivedLowerShriekBaseChangeMap A sq
  letI : IsIso E := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have hn : VectorIntegrationNormalization N hN A hA S hS d M c :=
    (existsUnique_vectorIntegrationGluing N hN A hA S hS d M).2.exists.choose_spec.2
  have hn' := hn t D W e
  change P.map c ≫ (ordinaryFiniteUnitPullback A W.ι).hom =
    E.app B ≫ F.map (vectorIntegrationChartCoefficient A N hA t S hS d M W e).hom ≫
      (affineLinearCompactComparison N hN A hA W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d).inv ≫
      affineTraceCounit A N hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d at hn'
  have hu : (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom = 𝟙 _ := by
    have h := (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom_inv_id
    rw [singleFunctorObjUnitIso_inv] at h
    exact (Category.comp_id _).symm.trans h
  have hm := frame_mate_units a b E B c
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom
    (ordinaryFiniteUnitPullback A W.ι).hom
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) W.toScheme).hom
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) W.ι).hom
    (vectorIntegrationChartCoefficient A N hA t S hS d M W e).hom
    ((affineLinearCompactComparison N hN A hA W.toScheme
      (affineTracePullbackInvertible N W.ι hS) d).inv ≫
      affineTraceCounit A N hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d) hn'
    (ordinaryFiniteUnitPullback_hom_unit A W.ι)
  erw [hu, Category.comp_id] at hm
  change _ ≫ (rightDerivedUpperShriekBaseChangeMap A sq).app (𝟙_ _) ≫
      (rightDerivedUpperShriek A (affineTraceProjection W.toScheme d)).map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) W.ι).hom = _ at hm
  dsimp only [vectorBundlePurityAdjunction]
  unfold dualizingComplexBaseChangeMap
  erw [hm]
  unfold CoordinateCounitArrows.towerAdjoint
  erw [Category.assoc
    (affineLinearCompactComparison N hN A hA W.toScheme
      (affineTracePullbackInvertible N W.ι hS) d).inv
    (affineTraceCounit A N hA t D W.toScheme
      (affineTracePullbackInvertible N W.ι hS) d)
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) W.toScheme).hom]
  have hc := congrArg Iso.hom (comp_transport A (affineTraceProjection W.toScheme d)
    W.ι (vectorIntegrationChart S d M W e ≫ VectorBundleZeroSection.π S d M)
    sq.w (affineLinearBaseCoefficient A N hA S d))
  dsimp only [Iso.trans_hom, Iso.app_hom] at hc
  dsimp only [vectorIntegrationChartCoefficient, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom]
  exact replace_middle_composite _ _ _ _ _ _ _ hc

set_option maxHeartbeats 800000 in
end AlgebraicGeometry.Etale
