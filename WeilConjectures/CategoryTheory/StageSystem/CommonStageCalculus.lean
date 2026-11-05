/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Data.Fintype.Order

import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Pbc.PbcExactCompletionData
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
/-! # The actual common-stage additive structure and shift

Source: blueprint `prop-weil-pbc-common-stage-calculus`.
(blueprint: prop-weil-pbc-common-stage-calculus)

These generic constructions apply to the canonical exact scalar-extension system.
They do not substitute an arbitrary system for the coefficient categories.
The sigma used in the representative formula is the adjunction mate of derived
scalar restriction's shift, restricted through the full integral inclusion and
then uniquely descended through rationalization. Thus it is fixed by the actual
tensor construction rather than supplied as an independent comparison.

## Main definitions and statements

* `pbcScalarCommShift`: the tensor-normalized finite-coefficient shift comparison.
* `pbcPairHasShift`: the coherent shift on the actual common-stage quotient.
* `CommonStageCalculusSpec`: the typed clause-by-clause common-stage assertion.
* `commonStageCalculus`: its specialization to the concrete PBC coefficient system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSectionVars false
universe c w u v
open CategoryTheory
open scoped ZeroObject
namespace CategoryTheory.ScalarLocalization
open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorShiftCore

end CategoryTheory.ScalarLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}
variable (T : Scheme.{u}) [IsNoetherian T]
  (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Signed reindexing preserves completion, bounded constructible reductions and
compatible etale origins. Source: blueprint orders 1308--1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: tensor with each finite quotient commutes with signed reindexing. Shift
all the bounded local models and all etale witnesses by the same integer; their
bounds translate by that integer and their quotient equations are unchanged.
The Koszul completion tower is shifted termwise, so its limit and unit shift too. -/
@[instance] theorem pbcIntegralStableShift (E : Padic.FiniteCoefficientFields l Ω) :
    ObjectProperty.IsStableUnderShift
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ℤ := by
  have := (cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T).2
  infer_instance

/-- The inherited shift remains linear for the actual constant-section action.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: scalar multiplication is degreewise multiplication on complexes. Signed
reindexing commutes with it. This passes to roofs in the ambient derived category
and restricts to the full integral subcategory. -/
@[instance] theorem pbcIntegralShiftLinear (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcStageDatum.{u} l Ω E)) :=
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)
  let R := PbcIntegralRing l (pbcFiniteField.{u} l Ω E)
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  refine ⟨fun f r ↦ P.ι.map_injective ?_⟩
  simp only [Functor.map_smul]

/-- The tensor Hom shift is additive. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: its normalized Hom action is ScalarLocalization.map, whose mapHom is linear. -/
@[instance] theorem pbcRationalShiftAdditive (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) n).Additive := by
  rw [((pbcRationalShift_exists l Ω T E).exists.choose_spec).1 n]
  infer_instance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Tensor balancing commutes with the normalized sigma comparisons.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the ambient associator is the mate of identity-on-sections restriction
composition, which commutes with signed reindexing. Restrict and rationalize
that equation; the normalizations of both comparisons preserve it. -/
@[instance] theorem pbcScalarAssociatorCommShift (h : E ≤ F) (k : F ≤ G) :
    NatTrans.CommShift (pbcScalarAssociator l Ω T hdim hl h k).hom ℤ := by
  have := cscIntegralAssociatorShift l Ω T hdim hl h k
  have hcomp (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F) :
      NatTrans.CommShift (pbcScalarIntegralComparison l Ω T hdim hl h).hom ℤ :=
    (pbcScalarShift_exists l Ω T hdim hl h).exists.choose_spec
  have := hcomp E F h
  have := hcomp F G k
  have := hcomp E G (h.trans k)
  exact ScalarLocalization.cscAssocShiftOfWhiskerLeft
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcScalarIntegralComparison l Ω T hdim hl k)
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k))
    (pbcIntegralScalarAssociator l Ω T hdim hl h k).hom
    (pbcScalarAssociator l Ω T hdim hl h k).hom
    (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec
    (fun X ↦ ⟨X.obj, 𝟙 _, by
      change IsIso ((pbcScalarExtension l Ω T hdim hl (h.trans k)).map (𝟙 X))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual raw rational stages have finite biproducts and a zero object.
Source: blueprint orders 1308--1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the zero complex and finite sums satisfy all three defining integral
conditions: their reductions, local finite models and etale witnesses are the
corresponding sums. Finite sums commute with the Koszul limit. Their inclusion
and projection maps obey the biproduct equations in the full subcategory.
Tensor these maps with one; the same five equations hold in the raw localization. -/
@[instance] theorem pbcStageFiniteBiproducts (E : Padic.FiniteCoefficientFields l Ω) :
    Limits.HasFiniteBiproducts (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) := by
  have h := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T
  have := h.1
  have := h.2
  let Q := pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)
  have : Q.EssSurj := ⟨fun K ↦ ⟨K.obj, ⟨Iso.refl _⟩⟩⟩
  have := Functor.hasFiniteProducts_of_additive_of_essSurj Q
  exact Limits.HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)

section Shift
variable [stageShift : ∀ i, HasShift (C i) ℤ]
    [transitionShift : ∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [associatorShift : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
include associatorShift

/-- The canonical HasShift structure; its object action is (E,K) ↦ (E,K[n]).
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
@[instance_reducible] def pbcPairHasShift : HasShift S.PairCategory ℤ :=
  hasShiftMk S.PairCategory ℤ (pbcPairShiftCore S)

attribute [instance] pbcPairHasShift

section AdditiveShift
variable [stagePreadditive : ∀ i, Preadditive (C i)]
    [transitionAdditive : ∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [stageShiftAdditive : ∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
include stagePreadditive transitionAdditive stageShiftAdditive

attribute [instance] pbcPairShift_additive

variable [∀ i, Limits.HasZeroObject (C i)]

end AdditiveShift
end Shift

section FiniteDiagrams
variable [Nonempty I]

variable [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, Limits.HasFiniteBiproducts (C i)]

/-- Finite direct sums descend without adjoining new objects.
Source: blueprint common-stage calculus (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: transport the finitely many objects to one stage and take their biproduct
there. Include its injections and projections in the pair category. To test the
biproduct equations or its universal property, transport the finitely many arrows
to one further stage. Additive transitions preserve finite biproducts, so the
finite-stage equations give exactly the required pair-category equations. -/
@[instance] theorem pbcPairFiniteBiproducts : Limits.HasFiniteBiproducts S.PairCategory := by
  classical
  constructor
  intro n
  constructor
  intro X
  obtain ⟨M, h⟩ := Finite.exists_le (fun a : Fin n ↦ (X a).stage)
  have : (S.ι M).Additive := by
    constructor
    intro A B f g
    simp only [ι_map_eq (le_refl M), Functor.map_add]
    exact ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ _ _).1
  let Y : Fin n → C M := fun a ↦ (X a).toStage (h a)
  have : Limits.HasProduct X := Limits.hasLimit_of_iso
    (F := Discrete.functor Y ⋙ S.ι M)
    (Discrete.natIso (fun a ↦ (S.isoToStage (X a.as) (h a.as)).symm))
  exact Limits.HasBiproduct.of_hasProduct X
end FiniteDiagrams

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
    [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, HasShift (C i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

open CategoryTheory.StageSystem

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
