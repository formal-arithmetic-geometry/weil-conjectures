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
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerRootScalarUnit
import Mathlib.CategoryTheory.Yoneda

/-! # The Tate root line in the specified scalar-adjunction presentation

Source: the coefficient-change paragraph of sk-prop-geo-p1-adjunction.proof.md
in literature/blueprint/latest/ (blueprint: geo-p1-scalar-line-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.GeoP1Adjunction

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem universal_transpose_isIso
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (R : D ⥤ C)
    (a : L ⊣ R) {X : C} {Y : D} (η : X ⟶ R.obj Y)
    (h : ∀ Z : D, Function.Bijective (fun f : Y ⟶ Z ↦ η ≫ R.map f)) :
    IsIso ((a.homEquiv X Y).symm η) := by
  apply isIso_of_coyoneda_map_bijective
  intro Z
  apply ((a.homEquiv X Z).bijective.of_comp_iff' _).mp
  simpa only [Function.comp_def, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply] using h Z

/-- The normalized root map determines an isomorphism from the actual derived
scalar extension, with its unit equation. Source: coefficient change in
sk-prop-geo-p1-adjunction.proof.md (blueprint: geo-p1-scalar-line-comparison).

Proof: use the existing root map, fixed on every pure root tensor, and its
unbounded scalar universal property. Take its transpose under the specified
scalar-change adjunction. Composing the adjunction Hom equivalence with
precomposition by this transpose is the universal-property bijection, so
precomposition is bijective for every test complex. The coyoneda criterion makes
the transpose invertible. The adjunction inverse law is the required unit equation.
This uses no flatness assumption on the coefficient homomorphism. -/
theorem exists_scalarLineComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∃ lineMap : Scheme.finiteEtaleTateLine T N A hA ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
          (Scheme.finiteEtaleTateLine T N B hB),
      (∀ (W : T.Etaleᵒᵖ) (a₀ : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
        lineMap.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W a₀ z) =
          Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a₀) z) ∧
      ∃ e : (Etale.scalarChangeSiteExtension φ T).obj
          (Etale.ordinaryFiniteLine A N hA T) ≅ Etale.ordinaryFiniteLine B N hB T,
        (Etale.scalarChangeSiteAdjunction φ T).unit.app
            (Etale.ordinaryFiniteLine A N hA T) ≫
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map e.hom =
        (DerivedCategory.singleFunctor _ 0).map lineMap ≫
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
            0).inv.app (Scheme.finiteEtaleTateLine T N B hB) := by
  obtain ⟨θ, hθ, hu⟩ := Etale.supported_kummer_root_scalar_unit φ T N hN hA hB hT
  let a := Etale.scalarChangeSiteAdjunction φ T
  let η := (DerivedCategory.singleFunctor _ 0).map θ ≫
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
      0).inv.app (Scheme.finiteEtaleTateLine T N B hB)
  unfold Etale.SupportedDerivedScalarUnit at hu
  have hu' := (SheafExactDegreeZero.scalarUniversal_iff T.smallEtaleTopology φ _ _ θ).mp
    (by exact hu)
  let f : (Etale.scalarChangeSiteExtension φ T).obj
      (Etale.ordinaryFiniteLine A N hA T) ⟶ Etale.ordinaryFiniteLine B N hB T :=
    (a.homEquiv _ _).symm η
  haveI hi : IsIso f := by
    apply universal_transpose_isIso _ _ a η
    intro K
    simpa only [η, Category.assoc] using hu' K
  refine ⟨θ, hθ, asIso f, ?_⟩
  exact (a.homEquiv _ _).apply_symm_apply η

end AlgebraicGeometry.ProEtale.GeoP1Adjunction
