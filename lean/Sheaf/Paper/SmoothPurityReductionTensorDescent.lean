/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SmoothPurityReductionStrictTensor

/-! # Descent of the specified strict reduction tensor comparison

Source: Stacks 07A4 and 0G7E; original node steps 1--5 and 8
(blueprint: lem-sp-reduction-tensor-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Descend a prescribed strict balancing comparison to the recorded reduction.
The source and target tensor models are inputs; the ordinary comparison and chain
isomorphism in the output are exactly the prescribed ones.
Source: Stacks 07A4, 0G7E, 03EL; original node steps 1--5 and 8
(blueprint: lem-sp-reduction-tensor-comparison-descent).

Proof: the sequence projection identifies the specified ordinary reduction with
ringed pullback by its tensor generator formula. Its universal left-derived pair
therefore identifies the recorded reduction and its counit with derived pullback,
using uniqueness of the counit-compatible comparison, on whole systems.
Pullback preserves flat-term K-flat representatives on the sequence site (0G7E).
For two source representatives their total is flat-term K-flat (07A2); thus all
three source computations and both target tensor computations are legitimate.
Use the prescribed inverse chain comparison to define the representative square.
Two-variable localization on the flat-term K-flat resolving subcategory extends
it to a natural isomorphism on the whole unbounded derived categories. Its square
is the displayed derived equation, with the specified counit, rather than an
inference from separately evaluated equalities. The normalized ringed derived
monoidal comparison supplies the strong monoidal structure. Its tensorator agrees
with the inverse of this isomorphism by the same representative square and descent
uniqueness. The associator equation is multiplication of three coefficients in
either order; the unit equation inserts 1. The input coherence records identify
these constraints with the actual signed-total associators and unitors, so the
construction works for any of the supplied normalized closed tensor models. -/
theorem sp_reduction_tensor_comparison_descent (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    (source : SpIntegralClosed l E T)
    (sourceModel : SemilinearSections.Models.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) source)
    (sourceSymmetry : @SymmetricCategory
      (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal)
    (sourceCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
      source sourceModel sourceSymmetry)
    (target : SpSystemClosed l E T)
    (targetModel : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) target)
    (targetSymmetry : @SymmetricCategory
      (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal)
    (targetCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
      target targetModel targetSymmetry) :
    ∃ (μ : source.tensor ⋙ spMonoidalReduction l E T D r ≅
        ((spMonoidalReduction l E T D r).prod (spMonoidalReduction l E T D r)) ⋙ target.tensor)
      (monoidal : @Functor.CoreMonoidal
        (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal
        (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal
        (spMonoidalReduction l E T D r)),
      let W : SpReductionMonoidalData l E T D r := {
        source := source
        sourceModel := sourceModel
        target := target
        targetModel := targetModel
        sourceSymmetry := sourceSymmetry
        sourceCoherence := sourceCoherence
        targetSymmetry := targetSymmetry
        targetCoherence := targetCoherence
        μ := μ
        monoidal := monoidal
        ordinary := C.ordinary
        chain := C.chain }
      SpReductionMonoidalTensor l E T D r W ∧
        ∃ hSystem : SpReductionSystemKflat l E T D r W,
          SpReductionDerived l E T D r W hSystem := by
  sorry

end AlgebraicGeometry.ProEtale
