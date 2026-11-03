/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunction
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
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
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.AffineIntegrationCoefficient.EtaleAffineIntegrationCoefficientEquation
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineProjectionCoefficientMate
import all WeilConjectures.AlgebraicGeometry.AffineIntegrationCoefficient.EtaleAffineIntegrationCoefficientEquation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all Mathlib.Logic.Small.Defs
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Data.PNat.Notation
import all WeilConjectures.Compactification.Defs

/-! # The affine-space dualizing coefficient mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 2--3
(blueprint: lem-coef-dualizing-affine-space).

## Main definitions

- `affineDualizingTowerComparison` and `affineDualizingTowerIso` fix tower coordinates.
- `AffineDualizingCoefficientAssertion` records the hypotheses and normalized conclusions.

## Main statements

- `affine_dualizing_coefficient` states invertibility of the specified coefficient mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance high] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The unbounded ordered coordinate-tower comparison, using the published
compactification, composition, and identity isomorphisms.
Source: blueprint affine-space reduction, proof step 1
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def affineDualizingTowerComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (r : ℕ) →
    affineTraceLeft A S r ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S r)
  | 0 => (unboundedEtaleLowerShriekId A S).symm
  | r + 1 =>
    letI := affineTraceNoetherian S r
    Functor.isoWhiskerRight
        (rightDerivedLowerShriekIso A
          (affineTraceLineCompactification (affineTraceTower S r)))
        (affineTraceLeft A S r) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S r) ↘ affineTraceTower S r))
        (affineDualizingTowerComparison A S r) ≪≫
      unboundedEtaleLowerShriekCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S r) ↘ affineTraceTower S r)
        (affineTraceProjection S r)

/-- Explicit passage from the degree-zero constant sheaf to the derived tensor unit.
Source: blueprint affine-space reduction, coefficient-unit convention
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def affineDualizingUnitIso
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ≅ 𝟙_ (DerivedCategoryModule A S) :=
  AffineIntegrationCoefficient.ordinaryUnitIso A S

/-- The chosen exceptional dualizing object identified with the ordered tower object
by uniqueness of right adjoints, including its counit.
Source: blueprint affine-space reduction, proof step 1
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def affineDualizingTowerIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) :
    dualizingComplex A (affineTraceProjection S r) ≅
      (affineTraceRight A N hA S r).obj (ordinaryFiniteUnit A S) :=
  ((rightDerivedUpperShriekAdjunction A
    (affineTraceProjection S r)).rightAdjointUniq
      ((affineTraceAdjunction A N hA t D S hS r).ofNatIsoLeft
        (affineDualizingTowerComparison A S r))).app (𝟙_ (DerivedCategoryModule A S)) ≪≫
    (affineTraceRight A N hA S r).mapIso (affineDualizingUnitIso A S).symm

/-- Identity-adjunction coordinates for the chosen dualizing object at the base.
Source: blueprint affine-space reduction, dimension-zero clause
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def affineDualizingZeroIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) : dualizingComplex A (𝟙 S) ≅
      𝟙_ (DerivedCategoryModule A S) :=
  ((rightDerivedUpperShriekAdjunction A (𝟙 S)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A S).symm)).app
      (𝟙_ (DerivedCategoryModule A S))

/-- Shift the canonical derived comparison of two degree-zero coefficient sheaves.
The shift constraint is the one transported through the exact scalar-restriction
adjunction. Source: blueprint affine-space reduction, proof step 2
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def affineDualizingShiftedSingleMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (c : (ProEtale.etaleSheafExtendScalars φ T).obj F ⟶ G) (d : ℤ) :
    (scalarExtension φ T).obj (((_root_.DerivedCategory.singleFunctor _ 0).obj F)⟦d⟧) ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦d⟧ :=
  (FiniteSmoothPurity.scalarShiftIso φ T d).hom.app _ ≫
    (shiftFunctor _ d).map
      (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T F ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map c)

/-- The ordinary rank-one tensor comparison is fixed at the constant coefficient
and the root generators, and then by the ordinary tensorator on every positive power.
Source: blueprint affine-space reduction, proof step 2
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def AffineDualizingTateNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (c : ∀ d : ℕ, (ProEtale.etaleSheafExtendScalars φ T).obj
      (Scheme.finiteEtaleTateTwist T N A hA d) ≅
        Scheme.finiteEtaleTateTwist T N B hB d) : Prop :=
  (∀ (W : T.Etaleᵒᵖ) (a : A),
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (c 0).hom).hom.app W
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app W (φ a)) ∧
  (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (c 1).hom).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z) ∧
  ∀ d : ℕ, (c (d + 2)).hom =
    Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars φ T)
      (Scheme.finiteEtaleTateTwist T N A hA (d + 1))
      (Scheme.finiteEtaleTateLine T N A hA) ≫
    tensorHom (c (d + 1)).hom (c 1).hom

/-- The specified counit equation and uniqueness of the affine-space coefficient mate.
The comparison is the published open/proper tensor arrow, with its total inverse
used only on the isomorphism domain. Source: blueprint affine-space reduction,
statement and proof step 5 (blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def AffineDualizingMateEquation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ)
    (v : (scalarExtension φ (affineTraceTower S r)).obj
      (dualizingComplex A (affineTraceProjection S r)) ⟶
        dualizingComplex B (affineTraceProjection S r)) : Prop :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S r)).map v ≫
      (rightDerivedUpperShriekAdjunction B
        (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule B S)) =
    ExceptionalCoefficients.comparisonInverse φ
        (HasCompactification.compactification (affineTraceProjection S r))
        (dualizingComplex A (affineTraceProjection S r)) ≫
      (scalarExtension φ S).map
        ((rightDerivedUpperShriekAdjunction A
          (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S))) ≫
      (ExceptionalCoefficients.unitIso φ S).hom

/-- Explicit normalization of the chosen-adjoint counit by the ordered coordinate trace.
The isomorphism to the tower object is the counit-compatible right-adjoint uniqueness
map, not an arbitrary identification of dualizing objects.
Source: blueprint affine-space reduction, proof step 1
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def AffineDualizingTraceNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u}) [IsNoetherian S]
    (N : ℕ) (hA : (N : A) = 0) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) : Prop :=
  (rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S)) =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S r)).map
        (affineDualizingTowerIso A N hA t D S hS r).hom ≫
      (affineDualizingTowerComparison A S r).inv.app
        ((affineTraceRight A N hA S r).obj (ordinaryFiniteUnit A S)) ≫
      affineTraceCounit A N hA t D S hS r ≫ (affineDualizingUnitIso A S).hom

/-- The eight conclusions of normalized affine dualizing coefficient change.
Source: blueprint affine-space reduction (blueprint: lem-coef-dualizing-affine-space). -/
structure AffineDualizingCoefficientConclusions
    (l : ℕ) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) : Prop where
  compactSupport_isIso :
    IsIso (ExceptionalCoefficients.compactSupportMap φ
      (HasCompactification.compactification (affineTraceProjection S r))
      (dualizingComplex A (affineTraceProjection S r)))
  dualizing_isIso :
    IsIso (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  mate_equation :
    AffineDualizingMateEquation φ S r
      (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  mate_unique :
    (∀ v, AffineDualizingMateEquation φ S r v →
      v = ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  counitA_isIso :
    IsIso ((rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S)))
  counitB_isIso :
    IsIso ((rightDerivedUpperShriekAdjunction B
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule B S)))
  trace_normalization :
    (∃ (e : ℕ) (hA : ((l ^ e : ℕ) : A) = 0) (hB : ((l ^ e : ℕ) : B) = 0)
        (hS : IsUnit ((l ^ e : ℕ) : Γ(S, ⊤)))
        (tA : OrdinaryFiniteTwistTransport A (l ^ e) hA)
        (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum A (l ^ e) hA tA T hT)
        (tB : OrdinaryFiniteTwistTransport B (l ^ e) hB)
        (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum B (l ^ e) hB tB T hT),
      AffineDualizingTraceNormalization A S (l ^ e) hA hS r tA DA ∧
      AffineDualizingTraceNormalization B S (l ^ e) hB hS r tB DB ∧
      Nonempty ((affineTraceRight A (l ^ e) hA S r).obj (ordinaryFiniteUnit A S) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA r))
            ⟦2 * (r : ℤ)⟧) ∧
      Nonempty ((affineTraceRight B (l ^ e) hB S r).obj (ordinaryFiniteUnit B S) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB r))
            ⟦2 * (r : ℤ)⟧) ∧
      ∃ c : ∀ d : ℕ,
        (ProEtale.etaleSheafExtendScalars φ (affineTraceTower S r)).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA d) ≅
            Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB d,
        AffineDualizingTateNormalization φ (affineTraceTower S r) (l ^ e) hA hB c ∧
        IsIso (affineDualizingShiftedSingleMap φ (affineTraceTower S r) (c r).hom
          (2 * (r : ℤ))))
  zero_normalization :
    (r = 0 →
      (ExceptionalCoefficients.unitIso φ S).inv ≫
          (scalarExtension φ S).map (affineDualizingZeroIso A S).inv ≫
          ExceptionalCoefficients.dualizingScalarMap φ (𝟙 S) ≫
          (affineDualizingZeroIso B S).hom = 𝟙 (𝟙_ (DerivedCategoryModule B S)))

/-- All clauses of affine-space coefficient reduction, on the actual ordinary etale
categories. The two finiteness premises have exactly the bounded constructible and
ordered finite-Tor-interval meaning in the node. The final equation is the literal
identity of B_s in identity-adjunction coordinates, without identifying chosen adjoints
definitionally. Source: blueprint affine-space reduction, statement
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def AffineDualizingCoefficientAssertion
    (l : ℕ) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) : Prop :=
  DerivedCategory.isBoundedConstructible A (affineTraceTower S r)
      (dualizingComplex A (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A (affineTraceTower S r) a b
      (dualizingComplex A (affineTraceProjection S r))) →
  DerivedCategory.isBoundedConstructible B (affineTraceTower S r)
      (dualizingComplex B (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn B (affineTraceTower S r) a b
      (dualizingComplex B (affineTraceProjection S r))) →
  AffineDualizingCoefficientConclusions l φ S r

private theorem counit_transport
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ H)
    (c : F' ≅ F) {U V : D} (e : U ≅ V) :
    a.counit.app V =
      F.map (((a.rightAdjointUniq (b.ofNatIsoLeft c)).app V ≪≫
        H.mapIso e.symm).hom) ≫
      c.inv.app (H.obj U) ≫ b.counit.app U ≫ e.hom := by
  have hn := (b.ofNatIsoLeft c).counit.naturality e.inv
  have hu := a.rightAdjointUniq_hom_app_counit (b.ofNatIsoLeft c) V
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  change F.map _ ≫ (c.inv.app (H.obj U) ≫ b.counit.app U) =
    (c.inv.app (H.obj V) ≫ b.counit.app V) ≫ e.inv at hn
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [F.map_comp]
  change F.map ((a.rightAdjointUniq (b.ofNatIsoLeft c)).app V).hom ≫
    c.inv.app (H.obj V) ≫ b.counit.app V = a.counit.app V at hu
  simp only [Category.assoc] at hu hn ⊢
  rw [reassoc_of% hn, reassoc_of% hu, e.inv_hom_id, Category.comp_id]

private theorem counit_transport_isIso
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ H)
    (c : F' ≅ F) {U V : D} (e : U ≅ V) [IsIso (b.counit.app U)] :
    IsIso (a.counit.app V) := by
  rw [counit_transport a b c e]
  infer_instance

private theorem left_uniq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem identity_interchange
    {C : Type*} [Category C] (F J : C ⥤ C) (e : J ≅ 𝟭 C) (t : F ≅ 𝟭 C) :
    Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F ≪≫ t =
      Functor.isoWhiskerLeft J t ≪≫ Functor.rightUnitor J ≪≫ e := by
  ext K
  change F.map (e.hom.app K) ≫ (𝟙 (F.obj K) ≫ t.hom.app K) =
    t.hom.app (J.obj K) ≫ (𝟙 (J.obj K) ≫ e.hom.app K)
  dsimp only [Functor.id_obj]
  rw [Category.id_comp, Category.id_comp]
  simpa only [Functor.id_obj, Functor.id_map] using t.hom.naturality (e.hom.app K)

private theorem identity_left_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] :
    ProEtale.reductionEtaleAffineLeftIso A S 0
      (HasCompactification.compactification (affineTraceProjection S 0)) =
      (unboundedEtaleLowerShriekId A S).symm := by
  have he : Adjunction.leftAdjointIdIso
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 S) inferInstance)
      (upperStarId (ModuleCat.{u + 1} A) S) =
      openImmersionLowerShriekId (ModuleCat.{u + 1} A) S := by
    unfold openImmersionLowerShriekId
    rw [left_uniq_conjugate]
    rfl
  have he' : Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 S))
      (upperStarId (ModuleCat.{u + 1} A) S) =
      openImmersionLowerShriekId (ModuleCat.{u + 1} A) S := by
    unfold openImmersionLowerShriekId
    rw [left_uniq_conjugate]
    rfl
  have ht := identity_tail_eq A S
  rw [he, he'] at ht
  change Functor.isoWhiskerLeft _ (rightDerivedLowerStarIdIso A S) ≪≫
    Functor.rightUnitor _ ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S = _ at ht
  apply Iso.ext_inv
  change ((rightDerivedLowerShriekOfCompactificationIso A
      (Compactification.ofIsProper (𝟙 S))
      (HasCompactification.compactification (𝟙 S))).inv ≫
    (Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
      Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).hom) = _
  unfold unboundedEtaleLowerShriekId
  rw [he, ← ht]
  change _ ≫ _ = _ ≫ _
  congr 1
  exact congrArg Iso.hom (identity_interchange _ _
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S)
    (rightDerivedLowerStarIdIso A S))

private theorem trace_normalization :
    AffineDualizingTraceNormalization A S N hA hS r t D := by
  unfold AffineDualizingTraceNormalization affineDualizingTowerIso
  exact counit_transport
    (rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S r))
    (affineTraceAdjunction A N hA t D S hS r)
    (affineDualizingTowerComparison A S r) (affineDualizingUnitIso A S)

private theorem tower_object (hN : 0 < N) :
    Nonempty ((affineTraceRight A N hA S r).obj (ordinaryFiniteUnit A S) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (affineTraceTower S r) N A hA r))
          ⟦2 * (r : ℤ)⟧) := by
  exact ⟨CoordinateCounitArrows.towerTateIso A N hN hA
    t S hS r⟩

private theorem mate_equation :
    AffineDualizingMateEquation φ S r
      (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r)) := by
  unfold AffineDualizingMateEquation
  rw [ExceptionalCoefficients.comparisonInverse_chosen_eq]
  exact ((ExceptionalCoefficients.chosenCompactSupportIso φ
    (affineTraceProjection S r)).app _).eq_inv_comp.mpr
      (ExceptionalCoefficients.tensor_unit_counit φ (affineTraceProjection S r))

private theorem mate_unique (v) (hv : AffineDualizingMateEquation φ S r v) :
    v = ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r) := by
  apply ((rightDerivedUpperShriekAdjunction B
    (affineTraceProjection S r)).homEquiv _ _).symm.injective
  have he := mate_equation φ S r
  unfold AffineDualizingMateEquation at hv he
  exact hv.trans he.symm

private theorem zero_purity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (N : ℕ) (hA : (N : A) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) :
    affineProjectionPurityIso A S 0 N hA hS t D =
      ((rightDerivedUpperShriekAdjunction A (𝟙 S)).rightAdjointUniq
        (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A S).symm)).symm := by
  unfold affineProjectionPurityIso
  rw [identity_left_comparison]
  unfold affineTraceAdjunction
  rfl

private theorem identity_mate
    {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) (GA : C ⥤ C) (GB : D ⥤ D)
    (eA : GA ≅ 𝟭 C) (eB : GB ≅ 𝟭 D) {U : C} {V : D} (q : Q.obj U ≅ V)
    (v : Q.obj (GA.obj U) ⟶ GB.obj (Q.obj U))
    (h : Q.map (eA.inv.app U) ≫ v = eB.inv.app (Q.obj U)) :
    q.inv ≫ Q.map (eA.inv.app U) ≫ (v ≫ GB.map q.hom) ≫ eB.hom.app V = 𝟙 V := by
  simp only [Category.assoc]
  rw [reassoc_of% h, ← eB.inv.naturality_assoc]
  simp

private theorem tate_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    ∃ c : ∀ d : ℕ, (ProEtale.etaleSheafExtendScalars φ T).obj
        (Scheme.finiteEtaleTateTwist T N A hA d) ≅
          Scheme.finiteEtaleTateTwist T N B hB d,
      AffineDualizingTateNormalization φ T N hA hB c ∧
      IsIso (affineDualizingShiftedSingleMap φ T (c r).hom (2 * (r : ℤ))) := by
  have hs : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  obtain ⟨_, c, hc, _⟩ :=
    WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization
      φ N hN hA hB T hs
  refine ⟨c, ?_, ?_⟩
  · unfold AffineDualizingTateNormalization
    refine ⟨?_, ?_, hc.1.2.2⟩
    · intro W a
      have h := hc.1.1 0 W a 1 (fun i ↦ Fin.elim0 i)
      rw [Adjunction.homEquiv_unit]
      change (c 0).hom.hom.app W
        (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app _).hom.app W
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a)) = _
      simpa only [one_smul, mul_one, _root_.id_eq, purityScalarSheafAdjunction,
        Scheme.finiteTateEtalePowerGenerator] using h
    · intro W a z
      have h := hc.1.1 1 W a 1 (fun _ ↦ z)
      rw [Adjunction.homEquiv_unit]
      change (c 1).hom.hom.app W
        (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app _).hom.app W
          (Scheme.finiteEtaleTateOneGenerator A N T hA W a z)) = _
      simpa only [one_smul, mul_one, _root_.id_eq, purityScalarSheafAdjunction,
        Scheme.finiteTateEtalePowerGenerator] using h
  · unfold affineDualizingShiftedSingleMap
    exact hc.2.1.2.1 r

private theorem zero_identity
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S]
    (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (h : (scalarExtension φ S).map
        ((affineProjectionPurityIso A S 0 N hA hS tA DA).hom.app
          (𝟙_ (DerivedCategoryModule A S))) ≫
        ExceptionalCoefficients.mateMap φ (𝟙 S) (𝟙_ (DerivedCategoryModule A S)) =
      (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS 0
        (𝟙_ (DerivedCategoryModule A S))).hom ≫
      (affineProjectionPurityIso B S 0 N hB hS tB DB).hom.app
        ((scalarExtension φ S).obj (𝟙_ (DerivedCategoryModule A S)))) :
    (ExceptionalCoefficients.unitIso φ S).inv ≫
        (scalarExtension φ S).map (affineDualizingZeroIso A S).inv ≫
        ExceptionalCoefficients.dualizingScalarMap φ (𝟙 S) ≫
        (affineDualizingZeroIso B S).hom = 𝟙 (𝟙_ (DerivedCategoryModule B S)) := by
  rw [zero_purity A S _ hA hS tA DA, zero_purity B S _ hB hS tB DB] at h
  have h' : (scalarExtension φ S).map
      (affineDualizingZeroIso A S).inv ≫
      ExceptionalCoefficients.mateMap φ (𝟙 S) (𝟙_ (DerivedCategoryModule A S)) =
    ((rightDerivedUpperShriekAdjunction B (𝟙 S)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId B S).symm)).inv.app
        ((scalarExtension φ S).obj (𝟙_ (DerivedCategoryModule A S))) := by
    unfold affineDualizingZeroIso
    change (scalarExtension φ S).map
        (((rightDerivedUpperShriekAdjunction A (𝟙 S)).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A S).symm)).inv.app _) ≫
        ExceptionalCoefficients.mateMap φ (𝟙 S) _ = _
    have hz : ProEtale.reductionEtaleAffineScalarIso φ S (N) hA hB hS 0
        (𝟙_ (DerivedCategoryModule A S)) = Iso.refl _ := by rfl
    rw [hz] at h
    simpa only [Iso.symm_hom, Iso.refl_hom, Category.id_comp] using h
  unfold affineDualizingZeroIso at h'
  rw [ExceptionalCoefficients.dualizingScalarMap_eq]
  unfold affineDualizingZeroIso
  exact identity_mate (scalarExtension φ S)
    (rightDerivedUpperShriek A (𝟙 S))
    (rightDerivedUpperShriek B (𝟙 S))
    ((rightDerivedUpperShriekAdjunction A (𝟙 S)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A S).symm))
    ((rightDerivedUpperShriekAdjunction B (𝟙 S)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId B S).symm))
    (ExceptionalCoefficients.unitIso φ S)
    (ExceptionalCoefficients.mateMap φ (𝟙 S) (𝟙_ (DerivedCategoryModule A S))) h'

private theorem finite_ring_assertion
    (l pchar : ℕ) [Fact l.Prime] (hp : 0 < pchar) (hl : l ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar]
    (hk : Finite k ∨ IsAlgClosed k)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (q : ℕ) (hA : ((l ^ q : ℕ) : A) = 0)
    (hB : ((l ^ q : ℕ) : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (hS : IsUnit ((l ^ q : ℕ) : Γ(S, ⊤))) (r : ℕ) :
    AffineDualizingCoefficientAssertion l φ S r := by
  classical
  let : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
  have hN : 0 < l ^ q := pow_pos (Fact.out : l.Prime).pos _
  obtain ⟨tA, DA, _, topA⟩ := exists_affineSpaceTopTrace _ hN A hA
  obtain ⟨tB, DB, _, topB⟩ := exists_affineSpaceTopTrace _ hN B hB
  have hnA := trace_normalization A _ hA tA DA S hS r
  have hnB := trace_normalization B _ hB tB DB S hS r
  have hεA : IsIso ((rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S))) := by
    let : IsIso ((affineTraceAdjunction A _ hA tA DA S hS r).counit.app
        (ordinaryFiniteUnit A S)) := (topA S hS r).2.2.1
    exact counit_transport_isIso
      (rightDerivedUpperShriekAdjunction A (affineTraceProjection S r))
      (affineTraceAdjunction A _ hA tA DA S hS r)
      (affineDualizingTowerComparison A S r) (affineDualizingUnitIso A S)
  have hεB : IsIso ((rightDerivedUpperShriekAdjunction B
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule B S))) := by
    let : IsIso ((affineTraceAdjunction B _ hB tB DB S hS r).counit.app
        (ordinaryFiniteUnit B S)) := (topB S hS r).2.2.1
    exact counit_transport_isIso
      (rightDerivedUpperShriekAdjunction B (affineTraceProjection S r))
      (affineTraceAdjunction B _ hB tB DB S hS r)
      (affineDualizingTowerComparison B S r) (affineDualizingUnitIso B S)
  have hunit := (AffineIntegrationCoefficient.property_iff A S _).2
    (AffineIntegrationCoefficient.ctf_iso A S (affineDualizingUnitIso A S)
      ((AffineIntegrationCoefficient.property_iff A S _).1
        (AffineIntegrationCoefficient.unit_property A S)))
  have hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A S a b
      (𝟙_ (DerivedCategoryModule A S)) := by
    obtain ⟨a, b, hab⟩ := hunit.2
    exact ⟨a, b, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr hab⟩
  have hMate := ordinaryAffineProjectionAssertion l pchar hp hl k hk
    A B φ q hA hB S hS r tA DA tB DB _ hunit.1 hTor
  have hIso : IsIso (ExceptionalCoefficients.dualizingScalarMap φ
      (affineTraceProjection S r)) := by
    let := hMate.2.1
    rw [ExceptionalCoefficients.dualizingScalarMap_eq]
    infer_instance
  unfold AffineDualizingCoefficientAssertion
  intro _ _ _ _
  refine ⟨?_, hIso, mate_equation φ S r, mate_unique φ S r, hεA, hεB, ?_, ?_⟩
  · exact (etaleCompactScalarCoherence φ _ _).1 _
  · refine ⟨q, hA, hB, hS, tA, DA, tB, DB, hnA, hnB,
      tower_object A _ hA tA S hS r hN, tower_object B _ hB tB S hS r hN, ?_⟩
    exact tate_normalization φ _ _ hN hA hB (affineTraceInvertible _ S hS r) r
  · intro hr
    subst r
    exact zero_identity A B φ S _ hA hB hS tA DA tB DB hMate.2.2

/-- The counit-defined reduction mate on affine r-space is invertible, with ordinary
finite Tate source, normalized coordinate trace, and the identity normalization at r=0.
Positive natural levels m,n encode exactly 1 ≤ m ≤ n; no flatness of the quotient is assumed.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 2--3
(blueprint: lem-coef-dualizing-affine-space).

Proof:
1. The coefficient rings are killed by a common positive power of l, invertible on
Spec k. Use the existing normalized coordinate traces and the uniqueness of right
adjoints to identify their counits with the chosen exceptional counits. Naturality
of the transported counit proves the stated trace equation. The canonical tower/Tate
isomorphism gives the shifted ordinary Tate objects.
2. The derived tensor unit is constructible and has finite Tor amplitude. Apply the
ordinary affine-projection coefficient mate theorem to it. This proves invertibility
of the specified mate, hence of the dualizing scalar map. The defining adjunction
bijection proves its counit equation and uniqueness. The compact-support coefficient
coherence supplies the compact-support clause on the assumed finite-Tor domain.
3. Apply finite Tate scalar source normalization. Its degree-zero and degree-one
generator formulas and tensor-power recursion give exactly the ordinary normalization
here; its line-map clause is the specified shifted single comparison.
4. In dimension zero the tower adjunction is the identity. Identify the published
compactification comparison with the identity comparison, using the identity tail
coherence and naturality of the direct-image identity. Right-adjoint uniqueness then
identifies the purity isomorphism with the inverse of the specified zero isomorphism.
The affine-projection mate equation, naturality and cancellation give the literal
identity on the coefficient unit. -/
theorem affine_dualizing_coefficient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : m ≤ n) (r : ℕ) :
    letI : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
      Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)
    letI : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) :=
      Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m m.property)
    AffineDualizingCoefficientAssertion l
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn)))
      (Spec (.of D.k)) r := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))
  let : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n n.property)
  let : Finite B := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E m m.property)
  let S := Spec (.of D.k)
  change AffineDualizingCoefficientAssertion l φ S r
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hz := (Scheme.sf_bc_adic_ring_domain l E).2.2.2.2.2.2.2.2.2
    n n.property
  have hA : ((l ^ (n : ℕ) : ℕ) : A) = 0 := by
    apply ULift.down_injective
    change ((l ^ (n : ℕ) : ℕ) : Padic.coefficientExtensionRing l E n) = 0
    simpa only [nsmul_eq_mul, mul_one] using hz.2.1 1
  have hB : ((l ^ (n : ℕ) : ℕ) : B) = 0 := by
    exact (map_natCast φ (l ^ (n : ℕ))).symm.trans
      ((congrArg φ hA).trans (map_zero φ))
  have hS : IsUnit ((l ^ (n : ℕ) : ℕ) : Γ(S, ⊤)) := by
    have hu : IsUnit ((l ^ (n : ℕ) : ℕ) : D.k) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : l.Prime) _hl.symm)).pow _
    simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  exact finite_ring_assertion l D.p D.prime.pos _hl D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) A B φ (n : ℕ) hA hB S hS r

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Trace
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
  (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
    OrdinaryFiniteP1Datum A N hA t T hT)
  (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ)

include hS t in
end Trace

section Mate
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ)

end Mate

section TateProof
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] ExceptionalCoefficients.unitIso
  ProEtale.pbcFixedScalarExtension derivedTensor
  Functor.leftAdjoint Functor.rightAdjoint Functor.leftDerivedFunctor
  Functor.mapDerivedCategory upperStar lowerStar
end TateProof

attribute [instance] CategoryTheory.catToReflQuiver
end AlgebraicGeometry.Etale
