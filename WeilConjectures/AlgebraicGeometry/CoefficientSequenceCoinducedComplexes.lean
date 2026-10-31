/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinduction
public import WeilConjectures.CategoryTheory.CoinducedSequenceProducts
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # The canonical two-term coinduced complex sequence

Source: Stacks 0941, 079P and 07A6.
(blueprint: def-coef-sequence-coinduced-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

/-- Countable products of complexes are computed degreewise in module sheaves.
Source: Stacks 0941 (blueprint: def-coef-sequence-coinduced-complexes). -/
instance complexProducts :
    HasCountableProducts (CochainComplex (coefficientSequenceModules l E W) ℤ) where
  out I _ := by
    have : Small.{u + 1} (Discrete I) := inferInstance
    have h : HasLimitsOfShape (Discrete I) (coefficientSequenceModules.{u, u} l E W) :=
      SheafOfModules.hasLimitsOfShape _ _
    exact @HomologicalComplex.instHasLimitsOfShape.{u + 1, u + 2, 0, 0, 0}
      _ _ _ _ _ _ _ h

/-- Degreewise exact evaluation of a coefficient sequence complex.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexEvaluation (n : ℕ) :=
  (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)

/-- Degreewise exact coinduction of a complex at a finite level.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexRight (n : ℕ) := (right l E W n).mapHomologicalComplex (.up ℤ)

/-- The termwise evaluation and coinduction adjunction.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexAdjunction (n : ℕ) := (adjunction l E W n).mapHomologicalComplex (.up ℤ)

/-- Degreewise restriction along the adjacent quotient map.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexRestriction (n : ℕ) :=
  (normalizedDVRModuleRes l E W (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)

/-- The actual adjacent coefficient transition on complexes.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexTransition (n : ℕ) :=
  (coefficientSequenceTransition l E W (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)

/-- The ordinary first coinduced product of a sequence complex.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexProduct (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  CoinducedSequence.product (complexEvaluation l E W) (complexRight l E W) K

/-- The ordinary product of coinduced adjacent relation objects.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexRelations (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  CoinducedSequence.relations (complexEvaluation l E W) (complexRight l E W)
    (complexRestriction l E W) K

/-- The termwise coinduced augmentation of a sequence complex.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexAugmentation (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  CoinducedSequence.augmentation (complexEvaluation l E W) (complexRight l E W)
    (complexAdjunction l E W) K

/-- The termwise adjacent compatibility difference.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev complexDifference (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  CoinducedSequence.difference (complexEvaluation l E W) (complexRight l E W)
    (complexAdjunction l E W) (complexRestriction l E W) (complexTransition l E W) K

/-- The concrete augmentation and difference form a short complex.
Source: Stacks 0941 (blueprint: def-coef-sequence-coinduced-complexes). -/
def complexSequence (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ShortComplex (CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  ShortComplex.mk (complexAugmentation l E W K) (complexDifference l E W K)
    (CoinducedSequence.augmentation_difference (complexEvaluation l E W)
      (complexRight l E W) (complexAdjunction l E W) (complexRestriction l E W)
      (complexTransition l E W) K)

/-- The sequence category has derived countable products.
Source: Stacks 079P (blueprint: lem-coef-sequence-derived-coinduced-comparison).
Proof: the module category of the essentially small ringed sequence site is
Grothendieck abelian in its coefficient universe. It has K-injective resolutions,
and products of K-injective complexes compute products in its derived category. -/
instance derivedProducts : HasCountableProducts (coefficientSequenceDerived l E W) := by
  have : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules l E W) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  exact ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩

/-- The product formed from the specified derived evaluation and coinduction.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev derivedProduct (N : coefficientSequenceDerived l E W) :=
  CoinducedSequence.product (coefficientSequenceDerivedEvaluation l E W)
    (derivedRight l E W) N

/-- The derived product of the adjacent scalar-restricted evaluations.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev derivedRelations (N : coefficientSequenceDerived l E W) :=
  CoinducedSequence.relations (coefficientSequenceDerivedEvaluation l E W)
    (derivedRight l E W) (fun n ↦ normalizedDVRRes l E W (Nat.le_succ n)) N

/-- The augmentation given by the specified derived adjunction units.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev derivedAugmentation (N : coefficientSequenceDerived l E W) :=
  CoinducedSequence.augmentation (coefficientSequenceDerivedEvaluation l E W)
    (derivedRight l E W) (derivedAdjunction l E W) N

/-- The difference given by the actual localized adjacent transition.
Source: Stacks 0941 and 015F (blueprint: def-coef-sequence-coinduced-complexes). -/
abbrev derivedDifference (N : coefficientSequenceDerived l E W) :=
  CoinducedSequence.difference (coefficientSequenceDerivedEvaluation l E W)
    (derivedRight l E W) (derivedAdjunction l E W)
    (fun n ↦ normalizedDVRRes l E W (Nat.le_succ n))
    (fun n ↦ coefficientSequenceDerivedTransition l E W (Nat.le_succ n)) N

end WeilConjectures.CoefficientCoinduction
