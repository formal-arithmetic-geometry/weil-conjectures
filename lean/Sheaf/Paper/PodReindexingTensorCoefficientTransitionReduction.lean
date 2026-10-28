/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.Paper.PodCompletionReindexCoefficientTransition

/-! # Reduction square component of the normalized coefficient transition

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-reduction).
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

/-- The reduction square component of a normalized coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-reduction).
Proof: choose a flat-term K-flat representative P of K and its whole-system
coherent quotient presentation. The quotient-generator and quotient-transition
laws for D and D′ identify their finite reindexing maps with the actual maps on
these quotients. The formula hpure identifies the two scalar/reindexing routes on
scalar-unit tensor generators. Balancedness extends this to all tensors, and
sheafification gives equality of the maps of module sheaves. Apply this degreewise
to P, retaining the actual quotient transition maps, to obtain equality of strict
systems. The scalar model normalization identifies its cochain scalar counit with
this same generator map, and its realization with the selected Roos comparison.
Thus applying the whole-system counit to the equality of strict maps gives the
claimed equality on P. The good-complex localization and naturality transport it
along a K-flat resolution to K. Expanding podScalarReduction gives the displayed
order of scalar completion, scalar realization, and counit. No choice of a new
completion reindexing family is made: the quotient and realization laws identify
the maps of the supplied D and D′ themselves.

Edge cases: for identity reindexing or identity scalar extension this is the
corresponding normalized identity square. The generator and localization argument
also applies to zero complexes and to the empty scheme; it uses no nonzero section
or nonempty-site assumption.
-/
theorem podReindexingTensorCoefficientTransition_reduction
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (hpure : ∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (S.ordinary.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) a x) :
    ∀ K : DerivedCategory (scalarReductionSource l E Y),
      (podScalarReduction l E L ι X D'.targetRoos S.target).app
          ((podOrdinaryReindex l E g).obj K) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          (D.reduction.inv.app K) ≫
        (integralComparisonSystemScalarPullback l E L ι g).hom.app
          ((podReindexCalculus l E Y).reduction.obj K) =
      (podReindexCalculus l L X).reduction.map
          ((S.derived l E L ι g D D').hom.app K) ≫
        D'.reduction.inv.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralComparisonDerivedSequencePullback l L g).map
          ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app K) := by
  sorry

end WeilConjectures
