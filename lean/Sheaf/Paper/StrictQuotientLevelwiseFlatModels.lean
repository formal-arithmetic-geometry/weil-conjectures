/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.StrictQuotientExpressions
import all Sheaf.Paper.PrimitiveQuotientRealizationComparisons
import all Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import all Sheaf.Paper.KFlatRingedToposPullback

/-! # Levelwise flat models of strict quotient complexes

Source: Stacks Project, Tags 0941, 07A2 and 0G7E.
(blueprint: lem-pur-strict-quotient-levelwise-flat-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Flat terms and K-flatness on the vertical sequence site can be checked at all
positive coefficient levels, with their actual coefficient actions.

Source: Stacks 0941, 07A2; the componentwise exactness and tensor argument in
lem-pur-quotient-expression-strict-kflat-towers, proof steps 7--8.
(blueprint: lem-pur-strict-quotient-levelwise-flat-models).

Proof: evaluation is exact and commutes with sheaf tensor and coproducts because
all covers are vertical. A term is flat if its evaluated terms are flat: tensor
a short exact sequence, evaluate, and use that the evaluations jointly detect
exactness. Conversely, place the flat system term in degree zero. This single complex
is K-flat, its evaluation remains K-flat, and the single-complex criterion
then proves flatness of the evaluated term. For an
acyclic system test complex, each evaluated total tensor is acyclic by level
K-flatness, and evaluation jointly detects acyclicity. Conversely lift an acyclic
level complex by the exact finite-prefix extension, apply system K-flatness, and
evaluate the total tensor. This uses no flatness of any coefficient quotient. -/
theorem levelwiseFlatModels (W : Scheme.{t}) (K : Complex l E W) :
    (∀ n : ℕ, Good l E K n) ↔
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) K ∧
      ∀ k : ℤ, SheafOfModules.IsFlatOnSite
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) (K.X k) := by
  constructor
  · intro hK
    exact ⟨sequenceKFlat_of_evaluations l E W K (fun n ↦ (hK n).1),
      fun k ↦ sequenceFlat_of_evaluations l E W (K.X k) (fun n ↦ (hK n).2 k)⟩
  · rintro ⟨hK, hf⟩ n
    refine ⟨(coefficientTensorModelPreservation l E W).2 K hK n, ?_⟩
    intro k
    let R := coefficientSequenceCommRingSheaf l E W
    let B := integralCoefficientCommRingSheaf l E W n
    let F := coefficientSequenceEvaluation l E W n
    let M := K.X k
    let S := (CochainComplex.singleFunctor (coefficientSequenceModules l E W) 0).obj M
    have hS : CochainComplex.IsKFlatIndependentCoefficients (R := R) S :=
      SheafOfModules.FlatSingleDerivedNormalization.single_kFlat R M (hf k)
    have hn := (coefficientTensorModelPreservation l E W).2 S hS n
    have ht := SheafOfModules.kFlat_iso_independent B
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) hn
    exact PrimitiveOrdinary.flat_of_single_kFlat (F.obj M) ht

end WeilConjectures.StrictQuotient
