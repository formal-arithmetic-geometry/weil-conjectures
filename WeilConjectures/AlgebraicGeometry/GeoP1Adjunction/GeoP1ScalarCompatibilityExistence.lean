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
import WeilConjectures.AlgebraicGeometry.GeoP1Adjunction.GeoP1ScalarLineComparison

/-! # An independent obligation for the projective-line adjunction

Source: the comparison and coefficient-change paragraphs of
sk-prop-geo-p1-adjunction.proof.md in literature/blueprint/latest/.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
namespace AlgebraicGeometry.ProEtale.GeoP1Adjunction

/--
Source:
literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-the-cycle-class-of-a-divisor-and-the-projective-line/
sk-prop-geo-p1-adjunction/sk-prop-geo-p1-adjunction.proof.md;
derived scalar extension and mate compatibility.

Proof in words:
1. The finite coefficient line is the scalar extension of the root sheaf from Z/N. The map induced
by phi sends a tensor a tensor z to phi(a) tensor z. The balancing relation makes it well-defined
without a flatness hypothesis; sheafification gives lineMap and the stated pure-root equation.
The existing supported_kummer_root_scalar_unit supplies this map and its derived universal
property. The proved exists_scalarLineComparison transports that property to the
scalarChangeSiteAdjunction used here, with its exact unit equation in degree zero.
Transport through the shift comparison before assembling the twisted tensor comparison.
2. Construct the direct-image scalar comparison as the adjunction mate of exact restriction of
scalars commuting with direct image. Properness and finite coefficients make this mate invertible.
Its adjunct equation is exactly the required direct-image unit normalization.
3. Construct the twisted inverse-image scalar comparison by derived tensor associativity, the
inverse-image scalar comparison, and scalar extension of the shifted root line. The root line is
locally free of rank one because N is invertible. Its scalar extension is therefore computed by
ordinary extension, even when phi is not flat. The universal scalar-adjunction unit and
restriction tensorator give exactly the displayed right comparison normalization.
4. Scalar extension preserves the Kummer class and the two normalized decomposition components.
Invert the resulting decomposition square and project to obtain the trace square. Paste this with
the proper projection square to get the actual counit equation. The unit equation follows by the
adjunction bijection, naturality, cancellation of the direct-image comparison and the two triangle
identities.
(blueprint: geo-p1-scalar-compatibility-existence)
-/
theorem exists_geoP1ScalarCompatibility (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) (hr : 0 < r)
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k) (hchar : (ℓ : k) ≠ 0)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) (hB : ((ℓ ^ r : ℕ) : B) = 0)
    (φ : A →+* B) (S : Base k)
    (hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S.scheme, ⊤))) :
    ScalarCompatibility φ (ℓ ^ r) (pow_pos hℓ.pos r) hA hB S.scheme hS := by
  sorry

end AlgebraicGeometry.ProEtale.GeoP1Adjunction
