/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.CompleteFlagBundle
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.SupportedProjectionSplitting
public import WeilConjectures.AlgebraicGeometry.SupportedHomPullback

import WeilConjectures.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.AlgebraicGeometry.KummerAdditivity
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.FiniteRingCompactSupportProjection
import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHom
import WeilConjectures.AlgebraicGeometry.ProEtaleModulePullbackComposition
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
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

/-!
# Complete-flag pullback with arbitrary closed support

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-localized-top-chern.proof.md`, Step 1
(blueprint: lem-pur-flag-pullback-injective).

The bounded monomials in the universal quotient Chern classes encode the iterated
projective-bundle decomposition. The exponents of Q_(i+1) range from zero to i.
The normalization kills every nonzero bounded monomial and retains the all-zero one.
The supported splitting is specified by this projection, the actual projection map,
and the normalized supported-Hom adjunction. No purity of the support is used.

## Main definitions

* `flagChernComponent`: the adjunct of a bounded quotient-line Chern monomial.
* `flagZeroComponent`: the all-zero component identification and zero on other words.
* `flagTwistPlus`: the signed finite Tate coefficient in the existing pro-etale D+.
* The imported `supportedProjectionSplitting` prescribes the induced supported splitting.

## Main statements

* `flag_pullback_split_injective`: split injectivity with the prescribed splitting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The list of quotient indices in a bounded Chern monomial.
Source: blueprint Step 1, iterated projective decomposition
(blueprint: lem-pur-flag-pullback-injective). -/
def flagChernWord (r : ℕ) (e : ℕ → ℕ) : List ℕ :=
  (List.range r).flatMap (fun i ↦ List.replicate (e i) i)

/-- Ordered cup product of a list of degree-two classes in a fixed power presentation.
Source: blueprint Step 1, Chern monomials
(blueprint: lem-pur-flag-pullback-injective). -/
def flagOrderedCup {C : Type v} [Category.{w} C] (tensor : C ⥤ C ⥤ C)
    (U L : C) (K : ℕ → C) (k0 : U ≅ K 0)
    (ks : ∀ n : ℕ, (tensor.obj (K n)).obj L ≅ K (n + 1))
    (delta : U ⟶ (tensor.obj U).obj U) (h : ℕ → (U ⟶ L)) :
    (l : List ℕ) → U ⟶ K l.length
  | [] => k0.hom
  | i :: l => delta ≫ (tensor.map (flagOrderedCup tensor U L K k0 ks delta h l)).app U ≫
      (tensor.obj (K l.length)).map (h i) ≫ (ks l.length).hom

/-- Multiply quotient Chern classes in the published positive shifted Tate powers.
Source: blueprint Step 1, the components of the iterated projective formula
(blueprint: lem-pur-flag-pullback-injective). -/
def flagWordCupRaw (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (T : Scheme.{u})
    (h : ℕ → (Etale.ordinaryFiniteUnit A T ⟶
      (Etale.ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧)) :
    (l : List ℕ) → Etale.ordinaryFiniteUnit A T ⟶
      (Etale.affineLinearBaseCoefficient A m hA) T l.length :=
  flagOrderedCup (Etale.ordinaryFiniteTensor A T) (Etale.ordinaryFiniteUnit A T)
    ((Etale.ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧)
    ((Etale.affineLinearBaseCoefficient A m hA) T) (Iso.refl _) (fun _ ↦ Iso.refl _)
    (projectiveBundleUnitDiagonal A T) h

/-- The Chern class of Q_(i+1), extended by zero beyond the rank for convenient indexing.
Only indices below r enter the word. Source: blueprint Step 1 and universal filtration
(blueprint: lem-pur-flag-pullback-injective). -/
def flagRootChern (P : PurityFiniteSetting.{u}) (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (b : T ⟶ Spec (.of P.field.k)) (i : ℕ) :
    Etale.ordinaryFiniteUnit P.Coefficient (completeFlagBundle r T F).scheme ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates (completeFlagBundle r T F).scheme)⟦(2 : ℤ)⟧ :=
  if hi : i < r then
    letI := (completeFlagBundle_properties r T F).2.2.1 i hi
    Etale.kummerFirstChern P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
      (completeFlagBundle r T F).scheme
      (P.diagonalExponent_isUnit ((completeFlagBundle r T F).projection ≫ b))
      (Scheme.Pic.ofIsInvertible (completeFlagQuotient r T F i))
  else 0

/-- The pro-etale component adjoint to the specified bounded Chern monomial.
Its degree-zero component is the actual adjunction unit after coefficient identification.
Source: blueprint Step 1, iterated projective-bundle decomposition
(blueprint: lem-pur-flag-pullback-injective). -/
def flagChernComponent (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (b : T ⟶ Spec (.of P.field.k)) (e : ℕ → ℕ) :
    P.projectiveBundleSummand T (flagChernWord r e).length ⟶
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (completeFlagBundle r T F).projection).rightDerivedFunctor.obj
        (P.projectiveBundleUnit (completeFlagBundle r T F).scheme) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
    (completeFlagBundle r T F).projection).homEquiv _ _
      (P.projectiveBundleSummandPullback t (completeFlagBundle r T F).projection
          (P.diagonalExponent_isUnit b) (flagChernWord r e).length ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          (completeFlagBundle r T F).scheme).mapDerivedCategory.map
            (P.projectiveBundleCupEvaluation (completeFlagBundle r T F).scheme
              (flagChernWord r e).length
              (flagWordCupRaw P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
                (completeFlagBundle r T F).scheme (P.flagRootChern r T F b)
                (flagChernWord r e))))

/-- The all-zero component's coefficient identification, and zero on other words.
Source: blueprint Step 1, projection onto the degree-zero summand
(blueprint: lem-pur-flag-pullback-injective). -/
def flagZeroComponent (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℕ) (e : ℕ → ℕ) :
    P.projectiveBundleSummand T (flagChernWord r e).length ⟶ P.projectiveBundleUnit T :=
  if h : (flagChernWord r e).length = 0 then
    eqToHom (congrArg (P.projectiveBundleSummand T) h) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
        (P.projectiveBundleCupEvaluation T 0 (𝟙 _))
  else 0

/-- The published signed finite Tate sheaf in pro-etale D+, with no restriction on a.
Source: blueprint Step 1, finite twist comparisons
(blueprint: lem-pur-flag-pullback-injective). -/
def flagTwistPlus (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℤ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent T
        P.diagonalExponent_annihilates a))

/-- Pullback is split injective for every closed support, degree and signed twist.
The retraction rho on Rp_* A kills precisely the nonzero bounded Chern components.
The equation for rK is the projection-formula prescription, written without choosing
an inverse projection map. The last equation specifies s by supported Hom and adjunction.
The target coefficient is the exact pullback of A_T(a), canonically A_T'(a).

Source: blueprint main-20261015, thm-pur-localized-top-chern.proof.md, Step 1
(blueprint: lem-pur-flag-pullback-injective).

Proof:
1. Ranks zero and one give the identity by def-pur-complete-flag-bundle. Otherwise
   recurse on its tautological kernel. Each projective stage is proper and remains
   separated and finite type by lem-pur-projective-bundle-tautological-geometry.
2. lem-asd-etale-finite-twist-pullback, lem-pur-kummer-additivity and the tensor
   comparison lem-weil-pbc-ringed-topoi-derived-tensor-pullback identify the signed
   finite twists with etale-origin constructible lines; negative powers use evaluation.
   lem-weil-pbc-comparison-pullback identifies their ordinary pro-etale pullbacks.
3. Iterate thm-pur-projective-bundle-formula. The monomials have exponents
   0 <= e_i <= i on Q_(i+1). The all-zero component is the adjunction unit.
   Projecting onto it gives rho with exactly the displayed component equations.
4. lem-sp-finite-ring-compact-support-projection, applied with identity open factor,
   makes the proper projection map invertible. Tensor rho by K and compose with
   its inverse and the unit action to obtain rK. The projection map's counit formula
   and the adjunction triangle identity give rK eta_K = identity.
5. lem-pur-supported-hom and lem-pur-supported-hom-pullback identify the actual
   supported pullback with the unit map on Hom from the closed constant sheaf.
   Adjunction followed by rK therefore gives s and s f* = identity, additively.
   These comparisons require no regularity or smoothness of Z.
6. lem-pur-proetale-module-pullback-composition identifies the composite supported
   pullback with flag pullback. The direct-image comparison of
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition identifies the iterated
   projections with the all-zero projection encoded by the component equations.
   This also proves that the splitting is precisely the one prescribed by the node. -/
theorem flag_pullback_split_injective (P : PurityFiniteSetting.{u})
    (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (bT : T ⟶ Spec (.of P.field.k))
    [IsSeparated bT] [LocallyOfFiniteType bT] [QuasiCompact bT]
    {Z Z' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ (completeFlagBundle r T F).scheme) [IsClosedImmersion i']
    (g : Z' ⟶ Z)
    (_sq : ChosenCartesianSquare g i' i (completeFlagBundle r T F).projection)
    (a b : ℤ) :
    ∃ t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates,
    P.supportedProjectionSplitting i i' (completeFlagBundle r T F).projection
      (P.flagTwistPlus T a) b (fun rho ↦
        ∀ w : ℕ → ℕ, (∀ j : ℕ, j < r → w j ≤ j) →
          P.flagChernComponent t r T F bT w ≫ rho = P.flagZeroComponent T r w) := by
  sorry

end WeilConjectures.PurityFiniteSetting
