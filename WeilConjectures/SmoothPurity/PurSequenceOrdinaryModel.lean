/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction

/-! # The ordinary completion model of given ordinary sequence adjoints

Source: Stacks 03D7 and 0941
(blueprint: lem-trf-completion-unit-ordinary-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The transported ordinary adjunction of `O` sends `x` to `1 ⊗ x` at every level.
Source: Stacks 03D7 and 0941
(blueprint: lem-trf-completion-unit-ordinary-adjunction). -/
theorem ordinaryAdjoints_unit_tensor (O : PurSequenceOrdinaryAdjoints l E W)
    (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    (((O.adjunction.ofNatIsoRight O.limit).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (O.pullback.obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (O.pullback.obj M) ≫
      (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x :=
  ordinary_unit_tensor l E W O M n V x

/-- The ordinary completion model whose tensor functor, evaluations, transitions and
adjunction are those of the given ordinary sequence adjoints `O`, transported along the
recorded limit identification, and whose termwise limit comparison is induced by `c`.
Source: Stacks 03D7 and 0941
(blueprint: lem-trf-completion-unit-ordinary-adjunction). -/
def ordinaryModelOfAdjoints (O : PurSequenceOrdinaryAdjoints l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n)) :
    OrdinaryModel l E W where
  tensor := O.pullback
  additive := O.pullback_additive
  evaluation := O.tensor
  transition := fun M {m n} h ↦ O.tensor_transition M m n h
  adjunction := O.adjunction.ofNatIsoRight O.limit
  unit_tensor := ordinaryAdjoints_unit_tensor l E W O
  limitComparison := Functor.isoWhiskerLeft (tower l E W) c
  limitComparison_projection := fun I n p ↦ hc ((tower l E W).obj I) n p

end WeilConjectures.CompletionUnit
