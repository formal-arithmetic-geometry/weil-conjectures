/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalChern
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionScalar
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionPullback
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.EssImageKernels
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquarePasting
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
public import WeilConjectures.AlgebraicGeometry.ScalarChangeAdjunctions
public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
public import WeilConjectures.AlgebraicGeometry.CartierDerivedRealization
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import
  WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalData
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalChernComponents
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # The classical projective-line trace adjunction

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-the-cycle-class-of-a-divisor-and-the-projective-line/sk-prop-geo-p1-adjunction/_section.md and
sk-prop-geo-p1-adjunction.proof.md, proposition and proof, (7.4)--(7.9)
(blueprint: sk-prop-geo-p1-adjunction).

The classical category is the full essential image of the whole unbounded etale
category. The specified unit is the supported diagonal composite. The counit is the
existing inverse-projection trace composite. Compatibility with scalar extension is
normalized by its adjunction units and the map on pure root tensors.

## Main definitions and statements

* `Classical`: the full essential image, with `pushClassical` and `rightClassical`.
* `ClassicalDatum`: the actual adjunction with its canonical comparison equations.
* `DiagonalUnit`, `BaseChange`, `ScalarCompatibility`: the stipulated map formulas.
* `exists_geoP1Adjunction`: all clauses of the projective-line proposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

namespace AlgebraicGeometry.ProEtale.GeoP1Adjunction

/-- The full essential image of unbounded etale comparison, as in the subsection's
standing conventions. Source: sk-prop-classical-inputs and the opening paragraph of
sk-prop-geo-p1-adjunction.proof.md (blueprint: sk-prop-geo-p1-adjunction). -/
abbrev Classical (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (geoP1Comparison A T).EssImageSubcategory

/-- The actual pro-etale twisted inverse image; the shifted Tate line is the
comparison pullback of the finite root line, without a trivialization.
Source: (7.4) (blueprint: sk-prop-geo-p1-adjunction). -/
def right (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) :=
  geoP1Pullback A (ProjectiveLine S ↘ S) ⋙
    (derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine S)).flip.obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2)

/-- Restriction of the actual derived direct image to its full classical categories.
Source: (7.4) (blueprint: sk-prop-geo-p1-adjunction). -/
def pushClassical (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (h : ∀ M : Classical A (ProjectiveLine S),
      (geoP1Comparison A S).essImage
        ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj M.obj)) :
    Classical A (ProjectiveLine S) ⥤ Classical A S :=
  (geoP1Comparison A S).essImage.lift
    ((geoP1Comparison A (ProjectiveLine S)).essImage.ι ⋙
      geoP1Pushforward A (ProjectiveLine S ↘ S)) h

/-- Restriction of twisted inverse image to the full classical categories.
Source: (7.4) (blueprint: sk-prop-geo-p1-adjunction). -/
def rightClassical (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (h : ∀ K : Classical A S,
      (geoP1Comparison A (ProjectiveLine S)).essImage ((right A N hA S).obj K.obj)) :
    Classical A S ⥤ Classical A (ProjectiveLine S) :=
  (geoP1Comparison A (ProjectiveLine S)).essImage.lift
    ((geoP1Comparison A S).essImage.ι ⋙ right A N hA S) h

/-- The canonical tensor and inverse-image map identifying the two twisted pullbacks.
Source: comparison transport in the proof's last paragraph
(blueprint: sk-prop-geo-p1-adjunction). -/
def rightComparisonMap (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (K : Etale.DerivedCategoryModule A S) :
    (geoP1Comparison A (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (right A N hA S).obj ((geoP1Comparison A S).obj K) :=
  letI : (comparisonUpperStar (ModuleCat.{u + 1} A) (ProjectiveLine S)).PreservesFlat :=
    preservesFlat_comparisonUpperStar
  (CategoryTheory.Functor.mapDerivedCategoryTensorComparison
      (comparisonUpperStar (ModuleCat.{u + 1} A) (ProjectiveLine S)) |>.app
        ((Etale.ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)).app
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine S)).map
      ((geoP1PullComparison A (ProjectiveLine S ↘ S)).inv.app K)).app
        (geoP1Twist A N hA (ProjectiveLine S) 1 2)

/-- The actual classical adjunction with both maps pinned to the ordinary normalized
maps through the canonical comparison. In particular, neither an arbitrary equivalence
nor an arbitrary adjunction is used as a substitute for the displayed maps.
Source: (7.4), (7.6), (7.7), comparison transport in the last paragraph
(blueprint: sk-prop-geo-p1-adjunction). -/
structure ClassicalDatum (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) where
  comparison_fullyFaithful : Nonempty (geoP1Comparison A S).FullyFaithful
  line_comparison_fullyFaithful :
    Nonempty (geoP1Comparison A (ProjectiveLine S)).FullyFaithful
  push_preserves : ∀ M : Classical A (ProjectiveLine S),
    (geoP1Comparison A S).essImage
      ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj M.obj)
  right_preserves : ∀ K : Classical A S,
    (geoP1Comparison A (ProjectiveLine S)).essImage ((right A N hA S).obj K.obj)
  adjunction : pushClassical A S push_preserves ⊣ rightClassical A N hA S right_preserves
  push_comparison : ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    IsIso (geoP1PushComparison A (ProjectiveLine S ↘ S) M)
  right_comparison : ∀ K : Etale.DerivedCategoryModule A S,
    IsIso (rightComparisonMap A N hA S K)
  unit_formula : ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    (adjunction.unit.app ((geoP1Comparison A (ProjectiveLine S)).toEssImage.obj M)).hom =
      (geoP1Comparison A (ProjectiveLine S)).map
          ((Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction.unit.app M) ≫
        rightComparisonMap A N hA S
          ((Etale.ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) ≫
        (right A N hA S).map (geoP1PushComparison A (ProjectiveLine S ↘ S) M)
  counit_formula : ∀ K : Etale.DerivedCategoryModule A S,
    geoP1PushComparison A (ProjectiveLine S ↘ S)
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ≫
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).map (rightComparisonMap A N hA S K) ≫
      (adjunction.counit.app ((geoP1Comparison A S).toEssImage.obj K)).hom =
    (geoP1Comparison A S).map
      ((Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app K)

/-- The unit of the fixed trace adjunction is exactly the supported diagonal unit,
with the canonical projection, exchange, and coefficient-line comparisons inserted.
Source: (7.6), first three proof paragraphs
(blueprint: sk-prop-geo-p1-adjunction). -/
def DiagonalUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  let p := ProjectiveLine S ↘ S
  let W := pullback p p
  let i := pullback.diagonal p
  let t := Etale.projectiveLineTraceTransport N hN A hA
  let L := (Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  ∃ (hI : i.ker.IsInvertible)
    (κ : Ext ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine W N A hA) 2),
    Etale.SupportedKummerBoundary A N hA i hI
      ((map_natCast ((pullback.fst p p) ≫ p).appTop.hom N) ▸
        hS.map ((pullback.fst p p) ≫ p).appTop.hom) κ ∧
    ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
      (Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction.unit.app M =
        (Etale.supportedDiagonalUnit A p L
          (Etale.ordinaryFiniteSupportedRealization A i
              (Scheme.finiteEtaleTateLine W N A hA) κ ≫
            (Etale.ordinaryFiniteDiagonalCoefficientIso A N hA t S hS true).inv)).app M ≫
          ((Etale.ordinaryFiniteTensor A (ProjectiveLine S)).obj
            ((Etale.ordinaryFinitePullback A p).obj
              ((Etale.ordinaryFinitePushforward A p).obj M))).map
            (Etale.ordinaryFiniteShiftedLinePullback A N hA t p hS).hom

/-- The two compatibility squares using the actual proper exchange and the
roots-normalized twisted-pullback comparison. The unit equation is written forward,
so no inverse exchange is hidden in a choice.
Source: base-change clause and final proof paragraph
(blueprint: sk-prop-geo-p1-adjunction). -/
def BaseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S] (g : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) : Prop :=
  let p := ProjectiveLine S ↘ S
  let gP := ProjectiveSpace.map (ULift.{u} (Fin 2)) g
  let t := Etale.projectiveLineTraceTransport N hN A hA
  let a := (Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction
  let a' := (Etale.projectiveLineTraceDatum N hN A hA S' hS').adjunction
  (∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    (Etale.ordinaryFinitePullback A gP).map (a.unit.app M) ≫
      (Etale.ordinaryFiniteP1RightBaseChange A N hA t g
        (Etale.ordinaryFiniteP1_isUnit N S hS)
        ((Etale.ordinaryFinitePushforward A p).obj M)).hom ≫
      (Etale.ordinaryFiniteP1Right A N hA S').map (Etale.ordinaryFiniteP1Exchange A g M) =
    a'.unit.app ((Etale.ordinaryFinitePullback A gP).obj M)) ∧
  (∀ K : Etale.DerivedCategoryModule A S,
    (Etale.ordinaryFinitePullback A g).map (a.counit.app K) =
      Etale.ordinaryFiniteP1Exchange A g ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ≫
        (Etale.ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (Etale.ordinaryFiniteP1RightBaseChange A N hA t g
            (Etale.ordinaryFiniteP1_isUnit N S hS) K).hom ≫
        a'.counit.app ((Etale.ordinaryFinitePullback A g).obj K))

/-- The map of shifted root lines induced by a specified map of the sheaves.
Source: the finite-coefficient clause, derived extension of the roots tensor
(blueprint: sk-prop-geo-p1-adjunction). -/
def shiftedScalarLine {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) (T : Scheme.{u})
    (lineMap : Scheme.finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB)) :
    (Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ ⟶
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
        ((Etale.ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧) :=
  (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map lineMap) ≫
    (cartierShiftSingleIso (Sheaf.restrictScalars T.smallEtaleTopology φ)
      (Scheme.finiteEtaleTateLine T N B hB)).inv

/-- Scalar extension comparisons normalized by their universal units. The line map
is fixed on every pure root tensor. These conditions fix both comparisons independently
of the projective-line adjunction; the last two equations assert compatibility of its
specified unit and counit. No flatness of the coefficient homomorphism is required.
Source: change-of-finite-coefficients clause, final proof paragraph
(blueprint: sk-prop-geo-p1-adjunction). -/
def ScalarCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  let P := ProjectiveLine S
  let p := P ↘ S
  let EA := Etale.ordinaryFiniteP1Right A N hA S
  let EB := Etale.ordinaryFiniteP1Right B N hB S
  let FA := Etale.ordinaryFinitePushforward A p
  let FB := Etale.ordinaryFinitePushforward B p
  let SX := Etale.scalarChangeSiteExtension φ P
  let SY := Etale.scalarChangeSiteExtension φ S
  let UX := Sheaf.derivedRestrictScalars P.smallEtaleTopology φ
  let UY := Sheaf.derivedRestrictScalars S.smallEtaleTopology φ
  let ax := Etale.scalarChangeSiteAdjunction φ P
  let ay := Etale.scalarChangeSiteAdjunction φ S
  let a := (Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction
  let b := (Etale.projectiveLineTraceDatum N hN B hB S hS).adjunction
  let R := Etale.scalarRestrictionDerivedTensorData
    (Sheaf.restrictScalars P.smallEtaleTopology φ)
    (sheafComposeLaxMonoidal P.smallEtaleTopology (ModuleCat.restrictScalars φ))
  ∃ (lineMap : Scheme.finiteEtaleTateLine P N A hA ⟶
      (Sheaf.restrictScalars P.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine P N B hB))
    (α : FA ⋙ SY ≅ SX ⋙ FB) (β : EA ⋙ SX ≅ SY ⋙ EB),
    (∀ (W : P.Etaleᵒᵖ) (a₀ : A) (z : (P.rootsOfUnitySheaf N).obj.obj W),
      lineMap.hom.app W (Scheme.finiteEtaleTateOneGenerator A N P hA W a₀ z) =
        Scheme.finiteEtaleTateOneGenerator B N P hB W (φ a₀) z) ∧
    (∀ M : Etale.DerivedCategoryModule B P,
      IsIso ((Etale.scalarRestrictionDirectImageMap φ p).app M)) ∧
    (∀ M : Etale.DerivedCategoryModule A P,
      ay.unit.app (FA.obj M) ≫ UY.map (α.hom.app M) ≫
          (Etale.scalarRestrictionDirectImageMap φ p).app (SX.obj M) =
        FA.map (ax.unit.app M)) ∧
    (∀ K : Etale.DerivedCategoryModule A S,
      ax.unit.app (EA.obj K) ≫ UX.map (β.hom.app K) =
        (((Etale.ordinaryFinitePullback A p).map (ay.unit.app K) ≫
          (Etale.scalarRestrictionPullbackIso φ p).hom.app (SY.obj K)) ⊗ₘ
          shiftedScalarLine φ N hA hB P lineMap) ≫
        R.map ((Etale.ordinaryFinitePullback B p).obj (SY.obj K))
          ((Etale.ordinaryFiniteLine B N hB P)⟦(2 : ℤ)⟧)) ∧
    (∀ M : Etale.DerivedCategoryModule A P,
      SX.map (a.unit.app M) ≫ β.hom.app (FA.obj M) ≫ EB.map (α.hom.app M) =
        b.unit.app (SX.obj M)) ∧
    (∀ K : Etale.DerivedCategoryModule A S,
      α.hom.app (EA.obj K) ≫ FB.map (β.hom.app K) ≫ b.counit.app (SY.obj K) =
        SY.map (a.counit.app K))

/-- Separated finite-type schemes over the standing field, packaged only to keep the
simultaneous coefficient and base-change quantifiers readable.
Source: standing conventions of sk-prop-classical-inputs
(blueprint: sk-prop-geo-p1-adjunction). -/
structure Base (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of k)
  separated : IsSeparated structureMap
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  quasiCompact : QuasiCompact structureMap

attribute [instance] Base.separated Base.locallyOfFiniteType Base.quasiCompact

/-- A simultaneous family of the actual classical trace adjunctions.
Source: (7.4) and its coefficient clause (blueprint: sk-prop-geo-p1-adjunction). -/
abbrev Family (k : Type u) [Field k] (N : ℕ) (hN : 0 < N) :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Base k) (hS : IsUnit (N : Γ(S.scheme, ⊤))),
    ClassicalDatum A N hN hA S.scheme hS

end AlgebraicGeometry.ProEtale.GeoP1Adjunction
