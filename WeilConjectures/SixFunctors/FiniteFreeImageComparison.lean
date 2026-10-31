/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.SixFunctors.EtaleOpenTensor
import WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import WeilConjectures.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Unbounded finite-free coefficient comparisons for direct image

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 1; Stacks 03CY, 03DI,
03DJ, 05DQ, 070I, 070K, 08BJ and 0944.
(blueprint: lem-sf-finite-free-image-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The actual basis insertion k maps to k tensor b, expressed by the scalar unit.
Source: blueprint finite-free-extension proof, paragraph 1; Stacks 05DQ
(blueprint: lem-sf-finite-free-image-comparison). -/
def finiteFreeImageBasisInclusion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    (T : Scheme.{u}) (b : B) (K : DerivedCategoryModule A T) :
    K ⟶ (Sheaf.derivedRestrictScalars T.smallEtaleTopology (algebraMap A B)).obj
      ((scalarExtension (algebraMap A B) T).obj K) :=
  (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (algebraMap A B))).unit.app K ≫
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (algebraMap A B)).map
      (b • 𝟙 ((scalarExtension (algebraMap A B) T).obj K))

/-- The compact-support coefficient comparison for the chosen compactification:
apply the ordinary projection comparison to p, then p_* to the canonical open comparison.
Source: blueprint finite-free-extension proof, paragraph 1, compact-support assembly
(blueprint: lem-sf-finite-free-image-comparison). -/
def finiteFreeCompactImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {V W : Scheme.{u}} {f : V ⟶ W} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ W ⟶
      scalarExtension φ V ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  Functor.whiskerLeft (derivedExtension (A := A) c.i) (scalarMate φ c.g) ≫
    Functor.whiskerRight (openScalarExtension φ c.i).hom
      (R(lowerStar (ModuleCat.{u + 1} B) c.g))

/-- Restriction for the chosen compact-support functor, pasted from the ordinary
restriction comparison and exact open extension's canonical restriction identification.
Source: blueprint finite-free-extension proof, paragraph 1; Stacks 03DI
(blueprint: lem-sf-finite-free-image-comparison). -/
def finiteFreeCompactRestrictionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {V W : Scheme.{u}} {f : V ⟶ W} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars V.smallEtaleTopology φ ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.whiskerLeft (derivedExtension (A := B) c.i)
      (scalarRestrictionDirectImageMap φ c.g) ≫
    Functor.whiskerRight
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ c.i).inv
      (R(lowerStar (ModuleCat.{u + 1} A) c.g))

/-- The finite-sum normalization and its inverse row, stated for a fixed pair of
image functors. The coordinates are the inverses of the basis insertion isomorphisms,
so they are precisely the coefficient projections, not arbitrary maps.
Source: blueprint finite-free-extension proof, paragraph 1, steps 5 and 7
(blueprint: lem-sf-finite-free-image-comparison). -/
def FiniteFreeImageCoordinates
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (basis : Module.Basis (Fin r) A B)
    {V W : Scheme.{u}}
    (FA : DerivedCategoryModule A V ⥤ DerivedCategoryModule A W)
    (FB : DerivedCategoryModule B V ⥤ DerivedCategoryModule B W)
    (eV : ∀ K : DerivedCategoryModule A V,
      (⨁ (fun _ : Fin r ↦ K)) ≅
        (Sheaf.derivedRestrictScalars V.smallEtaleTopology (algebraMap A B)).obj
          ((scalarExtension (algebraMap A B) V).obj K))
    (eW : ∀ K : DerivedCategoryModule A W,
      (⨁ (fun _ : Fin r ↦ K)) ≅
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology (algebraMap A B)).obj
          ((scalarExtension (algebraMap A B) W).obj K))
    (c : FA ⋙ scalarExtension (algebraMap A B) W ⟶
      scalarExtension (algebraMap A B) V ⋙ FB)
    (d : FB ⋙ Sheaf.derivedRestrictScalars W.smallEtaleTopology (algebraMap A B) ⟶
      Sheaf.derivedRestrictScalars V.smallEtaleTopology (algebraMap A B) ⋙ FA) : Prop :=
  ∀ K : DerivedCategoryModule A V,
    (∀ j : Fin r,
      finiteFreeImageBasisInclusion W (basis j) (FA.obj K) ≫
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology (algebraMap A B)).map
            (c.app K) ≫ d.app ((scalarExtension (algebraMap A B) V).obj K) =
        FA.map (finiteFreeImageBasisInclusion V (basis j) K)) ∧
    ((Sheaf.derivedRestrictScalars W.smallEtaleTopology (algebraMap A B)).map
          (c.app K) ≫ d.app ((scalarExtension (algebraMap A B) V).obj K)) ≫
        (biproduct.lift (fun j : Fin r ↦
          FA.map ((eV K).inv ≫ biproduct.π (fun _ : Fin r ↦ K) j)) ≫
          (eW (FA.obj K)).hom) = 𝟙 _ ∧
    (biproduct.lift (fun j : Fin r ↦
        FA.map ((eV K).inv ≫ biproduct.π (fun _ : Fin r ↦ K) j)) ≫
        (eW (FA.obj K)).hom) ≫
      ((Sheaf.derivedRestrictScalars W.smallEtaleTopology (algebraMap A B)).map
        (c.app K) ≫ d.app ((scalarExtension (algebraMap A B) V).obj K)) = 𝟙 _

/-- Finite-free extension commutes with arbitrary unbounded direct image and, for
Noetherian schemes and a chosen compactification, with compact support. The basis
coordinates, transpose and both inverse equations fix the canonical maps completely.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 1; Stacks 03CY, 03DI, 03DJ,
05DQ, 070I, 070K, 08BJ and 0944
(blueprint: lem-sf-finite-free-image-comparison).

Proof: (1) The basis and coefficient functionals give inclusions i_j and projections
p_j on sheafified scalar tensors, with p_j i_k = delta_jk and sum i_j p_j = 1.
Thus restriction of extension is a finite sum. Exact conservative restriction makes
extension exact, and the tensor/restriction adjunction descends termwise to all
unbounded complexes (lem-weil-pbc-exact-functor-derived-functor).
(2) Exact scalar extension implies restriction preserves K-injective complexes
(lem-weil-pbc-right-adjoint-preserves-kinjective). On a B-K-injective resolution,
restriction of direct image is literally direct image of restriction, by its
sectionwise formula. The two geometric adjunctions have the same underlying Hom
bijections (lem-weil-pbc-termwise-adjunction-homotopy and
lem-weil-pbc-kinjective-hom-derived), hence yield the displayed canonical mate.
(3) Direct image is additive. Its derived functor respects finite biproduct equations
by additive localization (lem-sfb-derived-localization-additive), including the empty sum.
(4) The pure-tensor pullback identification gives scalarMate as the B-adjunct of
extension of the A-counit, as in def-kun-projection-formula-map.
(5) The A-transpose of each restricted column is i_j followed by the A-counit;
counit naturality identifies it with Rf_*(i_j). Injectivity of the adjunction Hom
bijection gives the column equations. The finite-biproduct equations give the
inverse row Rf_*(p_j). Conservative exact restriction detects invertibility.
(6) Open extension and restriction of scalars commute on the defining extension
presheaf, identically on the open and uniquely on the zero terms off it. Sheafify
(lem-pc-sites-module-sheafification-interface) and descend termwise using exactness
(lem-weil-pbc-extension-by-zero-exact). The open tensor comparison of
lem-coef-etale-open-tensor sends m tensor b to itself and has the specified open
restriction normalization.
(7) Paste the comparison for p with that for j. Its columns are Rp_*j_!(i_j),
and its inverse row is Rp_*j_!(p_j), by step 5 and the open normalization in step 6.
This is finiteFreeCompactImageMap and finiteFreeCompactRestrictionMap. No boundedness
or cohomological-dimension condition was used. Structure maps to fields and closed
immersions are specializations with their chosen compactifications. -/
theorem finiteFreeImageComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B) :
    ∃ e : ∀ (T : Scheme.{u}) (K : DerivedCategoryModule A T),
        (⨁ (fun _ : Fin r ↦ K)) ≅
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology (algebraMap A B)).obj
            ((scalarExtension (algebraMap A B) T).obj K),
      (∀ (T : Scheme.{u}) (K : DerivedCategoryModule A T) (j : Fin r),
        biproduct.ι (fun _ : Fin r ↦ K) j ≫ (e T K).hom =
          finiteFreeImageBasisInclusion T (basis j) K) ∧
      (∀ {V W : Scheme.{u}} (f : V ⟶ W),
        IsIso (scalarRestrictionDirectImageMap (algebraMap A B) f) ∧
        IsIso (scalarMate (algebraMap A B) f) ∧
        (∀ K : DerivedCategoryModule A V,
          L(upperStar (ModuleCat.{u + 1} B) f).map
              ((scalarMate (algebraMap A B) f).app K) ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
              ((scalarExtension (algebraMap A B) V).obj K) =
            (scalarPullbackIso (algebraMap A B) f).hom.app
                ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
              (scalarExtension (algebraMap A B) V).map
                ((derivedUpperStarLowerStarAdjunction
                  (ModuleCat.{u + 1} A) f).counit.app K)) ∧
        FiniteFreeImageCoordinates basis
          (R(lowerStar (ModuleCat.{u + 1} A) f))
          (R(lowerStar (ModuleCat.{u + 1} B) f)) (e V) (e W)
          (scalarMate (algebraMap A B) f)
          (scalarRestrictionDirectImageMap (algebraMap A B) f)) ∧
      ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsNoetherian V] [IsNoetherian W]
        (c : Compactification f) [IsNoetherian c.Z],
        IsIso (finiteFreeCompactRestrictionMap (algebraMap A B) c) ∧
        IsIso (finiteFreeCompactImageMap (algebraMap A B) c) ∧
        OpenScalarExtensionNormalization (algebraMap A B) c.i
          (openScalarExtension (algebraMap A B) c.i) ∧
        (∀ P : DerivedCategoryModule A V,
          (derivedRestriction (A := B) c.i).map
              ((openScalarExtension (algebraMap A B) c.i).hom.app P) ≫
            (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} B) c.i).unit.app _)).inv =
            (openScalarRestriction (algebraMap A B) c.i).inv.app
                ((derivedExtension (A := A) c.i).obj P) ≫
              (scalarExtension (algebraMap A B) V).map
                (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) c.i).unit.app P)).inv) ∧
        (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          (upperStar (ModuleCat.{u + 1} B) c.i).map
              ((openScalarExtensionZero (algebraMap A B) c.i).hom.app M) ≫
            (asIso ((openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} B) c.i).unit.app _)).inv =
            (openScalarRestrictionZero (algebraMap A B) c.i).inv.app
                ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
              (ProEtale.etaleSheafExtendScalars (algebraMap A B) V).map
                (asIso ((openImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) c.i).unit.app M)).inv) ∧
        (∀ N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B),
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i).unit.app
              ((Sheaf.restrictScalars V.smallEtaleTopology (algebraMap A B)).obj N) ≫
            (upperStar (ModuleCat.{u + 1} A) c.i).map
              ((openImmersionLowerShriekRestrictScalarsIso (algebraMap A B) c.i).hom.app N) ≫
            (upperStarRestrictScalarsIsoSheaf (algebraMap A B) c.i).hom.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).obj N) =
            (Sheaf.restrictScalars V.smallEtaleTopology (algebraMap A B)).map
              ((openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} B) c.i).unit.app N)) ∧
        (∀ (Z : Scheme.{u}) (t : Z ⟶ c.Z),
          Disjoint (Set.range c.i.base) (Set.range t.base) →
          (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
            (upperStar (ModuleCat.{u + 1} B) t).map
              ((openScalarExtensionZero (algebraMap A B) c.i).hom.app M) = 0) ∧
          (∀ N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B),
            (upperStar (ModuleCat.{u + 1} A) t).map
              ((openImmersionLowerShriekRestrictScalarsIso
                (algebraMap A B) c.i).hom.app N) = 0)) ∧
        FiniteFreeImageCoordinates basis
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c)
          (e V) (e W) (finiteFreeCompactImageMap (algebraMap A B) c)
          (finiteFreeCompactRestrictionMap (algebraMap A B) c) := by
  sorry

end AlgebraicGeometry.Etale
