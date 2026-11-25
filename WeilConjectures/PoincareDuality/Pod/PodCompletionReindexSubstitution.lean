/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution

/-! # Coherence of the specified ordinary reindexing comparisons

Defines `PodReindexSubstitution`, the property that a normalized ordinary reindexing comparison
along an isomorphism `g` is realized by a family of completed operation models on the source and
target of `g`.

## Implementation details

All equations refer to the family's own reduction, limit and tensor maps. The tensor codomain
comparisons are isomorphisms of presentations, obtained from uniqueness of adjoints, rather
than equalities of chosen tensor functors.

## References

* Stacks Project, Tags 03EL, 07A4, 08J9, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b s
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The two locations `X` (for `true`) and `Y` (for `false`) of the source and target systems. -/
def podReindexLocations (X Y : Scheme.{u}) : Bool → Scheme.{u} :=
  fun b ↦ if b then X else Y

/-- The comparison of a model's tensor codomain with the fixed quotient/Roos tensor codomain,
built from the comparison of closed structures and uniqueness of left adjoints. -/
def podReindexTensorCodomainComparison {S : Type s} {W : S → Scheme.{u}}
    (C : CompletedOperations.Models l E W) (a : S) :
    ((C.calculus a).reduction.prod (C.calculus a).reduction) ⋙
        CompletedOperations.tensor l E C a ⋙ coefficientSequenceLimit l E (W a) ≅
      pullbackTensorReferenceTensor l E (W a) :=
  isoWhiskerRight
    (isoWhiskerLeft ((C.calculus a).reduction.prod (C.calculus a).reduction)
        (CoefficientClosedStructure.comparison (C.system a).closed
          (pullbackTensorCalculus l E (W a)).systemClosed) ≪≫
      isoWhiskerRight
        (NatIso.prod
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction)
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction))
        (pullbackTensorCalculus l E (W a)).systemClosed.tensor)
    (coefficientSequenceLimit l E (W a))

/-- Substitution for the normalized primitives `D` and `T`: there is a family of completed
operation models whose calculi, completion augmentations, Roos models and pullback realization
are those of `D`, whose tensor realizations match the integral tensor models, whose pullback
comparison recovers `D.limit`, and which satisfies the expression laws together with
`T.Model` and `T.Canonical`. -/
def PodReindexSubstitution {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D) : Prop :=
  ∃ C : CompletedOperations.Models l E (podReindexLocations X Y),
    ∃ qY : integralCompletedTensor l E Y ≅ IntegralOnSlice.completedTensor l E Y none,
    ∃ qX : integralCompletedTensor l E X ≅ IntegralOnSlice.completedTensor l E X none,
    C.calculus false = podReindexCalculus l E Y ∧
    C.calculus true = podReindexCalculus l E X ∧
    HEq (C.completion false) D.completionSource ∧
    HEq (C.completion true) D.completionTarget ∧
    C.roos false = D.sourceRoos ∧ C.roos true = D.targetRoos ∧
    HEq (C.pullback (a := true) (b := false) g).realization D.pullback ∧
    (qY ≪≫ CompletedOperations.tensorRealization l E C false ≪≫
      podReindexTensorCodomainComparison l E C false) =
        pullbackTensorIntegralTensorModel l E Y ∧
    (qX ≪≫ CompletedOperations.tensorRealization l E C true ≪≫
      podReindexTensorCodomainComparison l E C true) =
        pullbackTensorIntegralTensorModel l E X ∧
    (∀ N : coefficientSequenceDerived l E Y,
      IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
          D.limit.hom.app N) ∧
    PodCompletedTensorReindex.Model l E g D T ∧
    PodCompletedTensorReindex.Canonical l E g D T ∧
    CompletedOperations.ComparisonLaws.{u,u,0,0} l E C ∧
    CompletedOperations.SubstitutionLaw.{u,u,0,0,0} l E C ∧
    CompletedOperations.StructuralLaw.{u,u,0,0} l E C

end WeilConjectures
