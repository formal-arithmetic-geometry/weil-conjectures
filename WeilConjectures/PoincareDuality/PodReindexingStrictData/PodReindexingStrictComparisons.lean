/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingGoodComplex
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRestrictedTower
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosShiftCompatibility

/-! # Strict quotient and Roos reindexing before localization

## References

* [Stacks: Tags 03D6, 03EL, 07A4, 0941]
* [Bhatt--Scholze, *The pro-étale topology for schemes*, 6.5.9(4)]
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Strict Roos and restricted-tower comparisons before localization. -/
structure PodReindexingStrictData where
  /-- The same natural Roos map on all strict towers, including incomplete inputs. -/
  roos : ∀ C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ,
    (isoReductionIntegralComplex l E g).obj (integralOperationsRoos C) ≅
      integralOperationsRoos ((podReindexTower l E g).obj C)
  /-- Restriction and reindexing commute on the whole strict tower of complexes. -/
  restricted : ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    (podReindexTower l E g).obj (podRestrictedTower l E C) ≅
      podRestrictedTower l E
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C)

/-- Reindexing preserves good representatives. -/
theorem PodReindexingStrictData.good (_D : PodReindexingStrictData l E g)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    integralOperationsGoodComplex l E X ((isoReductionIntegralComplex l E g).obj P) :=
  podReindexingGoodComplex l E g P hP

/-- The Roos comparison of `D` has the prescribed first cone coordinate. -/
def PodReindexingStrictData.RoosFst (D : PodReindexingStrictData l E g) : Prop :=
  ∀ C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ,
    (D.roos C).hom ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary ((podReindexTower l E g).obj C)) =
      (isoReductionIntegralComplex l E g).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫ podReindexProduct l E g C

/-- The Roos comparison of `D` has the prescribed second cone coordinate, in degree `i - 1`. -/
def PodReindexingStrictData.RoosSnd (D : PodReindexingStrictData l E g) : Prop :=
  ∀ (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (i : ℤ),
    (D.roos C).hom.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary ((podReindexTower l E g).obj C))).v i (i - 1) (by omega) =
      (isoReductionIntegralInverse l E g).map
        ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          i (i - 1) (by omega)) ≫ (podReindexProduct l E g C).f (i - 1)

/-- The Roos comparison of `D` is natural on entire strict towers. -/
def PodReindexingStrictData.RoosNaturality (D : PodReindexingStrictData l E g) : Prop :=
  ∀ (C C' : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ)
    (a : C ⟶ C'),
    (isoReductionIntegralComplex l E g).map (integralOperationsRoosMap a) ≫
        (D.roos C').hom =
      (D.roos C).hom ≫ integralOperationsRoosMap ((podReindexTower l E g).map a)

/-- The Roos comparison of `D` is compatible with the signed mapping-cocone shifts. -/
def PodReindexingStrictData.RoosShift (D : PodReindexingStrictData l E g)
    (SY : PodSignedRoosShift (scalarReductionSource l E Y))
    (SX : PodSignedRoosShift (scalarReductionSource l E X)) : Prop :=
  ∀ (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (r : ℤ),
    ((D.roos (podShiftTower C r)).hom ≫
      integralOperationsRoosMap (podTowerShift l E g C r).hom ≫
      (SX.comparison ((podReindexTower l E g).obj C) r).hom) =
      ((isoReductionIntegralComplex l E g).map (SY.comparison C r).hom ≫
        ((isoReductionIntegralComplex l E g).commShiftIso r).hom.app
          (integralOperationsRoos C) ≫ (D.roos C).hom⟦r⟧')

/-- The restricted comparison of `D` is the inverse-image unit on every restricted section. -/
def PodReindexingStrictData.RestrictedGenerators (D : PodReindexingStrictData l E g) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (C.X i).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
    (((D.restricted C).hom.app (op n)).f i).val.app (op U)
        (integralComparisonRestrictedSection l E Y (C.X i) n
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj (C.X i)) n (op U)
        (((integralComparisonSequencePullback l E g).obj (C.X i)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (C.X i) n
            ((proEtaleIsoPostcompose g).obj U) x))

/-- The laws of strict reindexing data: both cone coordinates, naturality, shift compatibility
and the restricted generator formula. -/
def PodReindexingStrictData.Laws (D : PodReindexingStrictData l E g)
    (SY : PodSignedRoosShift (scalarReductionSource l E Y))
    (SX : PodSignedRoosShift (scalarReductionSource l E X)) : Prop :=
  D.RoosFst l E g ∧ D.RoosSnd l E g ∧ D.RoosNaturality l E g ∧
  D.RoosShift l E g SY SX ∧
  D.RestrictedGenerators l E g

/-- There are strict Roos and restricted-tower comparisons satisfying all the laws, for any
signed Roos shifts `SY`, `SX` satisfying their laws. -/
theorem podReindexingStrictComparisons
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SY : PodSignedRoosShift (scalarReductionSource l E Y))
    (SX : PodSignedRoosShift (scalarReductionSource l E X))
    (hSY : SY.Laws) (hSX : SX.Laws) :
    ∃ D : PodReindexingStrictData l E g, D.Laws l E g SY SX := by
  let F := isoReductionIntegralInverse l E g
  have : F.IsEquivalence := isoReduction_equivalence.{t, u} g
    (isoReductionCompletedMap l E g).hom
  have hi (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) :
      IsIso (scalarRoosMap F C) := podReindexingRoosComparison F C
  let roos (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) :=
    @asIso _ _ _ _ (scalarRoosMap F C) (hi C)
  obtain ⟨restricted, hrestricted⟩ := podReindexingRestrictedTower l E g
  refine ⟨⟨roos, restricted⟩, ?_, ?_, ?_, ?_, hrestricted⟩
  · intro C
    exact (podReindexingRoosCoordinates F C).1
  · intro C i
    exact (podReindexingRoosCoordinates F C).2 i
  · intro C C' a
    exact podReindexingRoosNaturality F a
  · exact podReindexingRoosShiftCompatibility l E g SY SX hSY hSX

end WeilConjectures
