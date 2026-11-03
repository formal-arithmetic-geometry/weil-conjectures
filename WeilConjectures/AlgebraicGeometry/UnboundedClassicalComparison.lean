/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules

import WeilConjectures.AlgebraicGeometry.UnboundedClassicalUnit
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison

/-!
# Unbounded finite-coefficient pro-étale comparison

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-unbounded/sk-prop-pe-unbounded-classical/_section.md,
Proposition `sk-prop-pe-unbounded-classical` (blueprint: sk-prop-pe-unbounded-classical).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The unbounded finite-coefficient comparison is fully faithful, preserves arbitrary
coproducts, and commutes with finite-type direct image.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-unbounded/sk-prop-pe-unbounded-classical/_section.md,
Proposition `sk-prop-pe-unbounded-classical` (blueprint: sk-prop-pe-unbounded-classical).

Proof: the uniform cohomological bounds and the fixed-degree truncation statement reduce
both the unit and direct-image assertions degree by degree to the bounded-below comparison.
The unbounded unit result gives full faithfulness of the comparison inverse image, and its
left-adjoint presentation gives preservation of every discrete colimit, hence arbitrary
direct sums. The direct-image assertion is the canonical mate (2.9), represented by
`unboundedDirectImageComparisonMap`, whose bounded-below invertibility extends to every
unbounded complex by the same truncation argument.
-/
theorem unboundedClassicalComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType g] [QuasiCompact g]
    : Nonempty
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.FullyFaithful ∧
      (∀ I : Type v, Nonempty (PreservesColimitsOfShape (Discrete I)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory)) ∧
      (∀ K : DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        IsIso (unboundedDirectImageComparisonMap A g K)) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let E := finiteCoefficientRealization X A
  obtain ⟨_, ⟨h⟩, _⟩ := unboundedClassicalUnit.{u, v} k hbase hℓ A hA X
  have hcomp : (L.mapDerivedCategory ⋙ E.mapDerivedCategory).FullyFaithful :=
    h.ofIso (Functor.mapDerivedCategoryCompIso L E)
  refine ⟨⟨Functor.FullyFaithful.ofCompFaithful hcomp⟩, ?_, fun K ↦
    unboundedDirectImageComparison k hbase hℓ A hA g K⟩
  intro I
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  exact ⟨adj.leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

end AlgebraicGeometry.ProEtale
