/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarColimits

/-! # Duality for normalized point evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

/-- Duality and reparametrization for normalized component evaluation.
Source: blueprint local boundary duality, Step 5 and its Frobenius paragraph.
Split projective cohomology to represent a constructible complex on each component by a
bounded zero-differential finite free complex. Glue these models. The ringed-site bounded
free Hom model computes its internal dual, which is again bounded constructible. Apply
sections: the result is the ordinary finite free dual, so the canonical transpose comparison
is invertible. The signed chain evaluation formulas on both sides agree on every homogeneous
pure tensor; this proves the evaluation square. Precomposition by a matrix gives naturality.
A field automorphism fixes constant coefficient sections, and a permutation reindexes
components. Pullback composition and the pure-tensor formulas give the normalized section
reindexing isomorphism, its monoidality and its duality square. Passing through the Hom
models preserves these equalities, so the conclusions are independent of the chosen bases.
The canonical normalization hypothesis is needed to identify the tensor and unit maps.
(blueprint: lem-a1-condensed-point-normalized-duality) -/
theorem condensed_point_normalized_duality
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (hs : IsCanonicalCondensedBoundaryEvaluationTensor ℓ k I) :
    CondensedBoundaryDualConstructibleAssertion ℓ k I ∧
      CondensedBoundaryDualIsIsoAssertion ℓ k I ∧
      CondensedBoundaryEvaluationAssertion ℓ k I ∧
      CondensedBoundaryDualNaturalityAssertion ℓ k I ∧
      CondensedBoundaryReparametrizationAssertion ℓ k I := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
