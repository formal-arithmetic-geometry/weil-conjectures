/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.SixFunctors.CompletedTensorShiftRight
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.CategoryTheory.Shift.CommShift
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus

/-!
# Shift squares for the specified single-operation integral comparisons

Source: main-20261015, sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md,
maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift).

The tensor constructors distinguish the selected slot. Their other operand is an
integral input and its actual reduction is the other system operand. The comparison
is exactly GeneratorReduction.pullD, identity for the defining proper tower,
GeneratorReduction.openD, or GeneratorReduction.tensorD.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A basic operation with one selected input slot; the two tensor slots are distinct.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
inductive BasicShiftOperation (B : Scheme.{u}) : Over B → Over B → Type (u + 3) where
  | pull {U V : Over B} (f : U ⟶ V) (hs : IsSeparated f.left)
      (ht : LocallyOfFiniteType f.left) (hq : QuasiCompact f.left) : BasicShiftOperation B V U
  | push {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left) : BasicShiftOperation B U V
  | open {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) : BasicShiftOperation B U V
  | tensorLeft (W : Over B) (N : Integral l E W.left) : BasicShiftOperation B W W
  | tensorRight (W : Over B) (M : Integral l E W.left) : BasicShiftOperation B W W

variable {B : Scheme.{u}} {U V : Over B}

/-- The actual strict-system operation in the selected slot.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.system (o : GeneratorReduction.Operations l E) :
    BasicShiftOperation l E B U V → (System l E U.left ⥤ System l E V.left)
  | .pull f _ _ _ => IntegralSystemRealization.pull l E f.left
  | .push f _ => Operations.push l E o.system f.left
  | .open j hj _ => letI := hj; Operations.shriek l E o.system j.left
  | .tensorLeft W N =>
      (Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj
        ((calculus l E W.left).reduction.obj N)
  | .tensorRight W M =>
      (Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj
        ((calculus l E W.left).reduction.obj M)

/-- The corresponding completed integral operation, with the generator's proper tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.integral (o : GeneratorReduction.Operations l E) :
    BasicShiftOperation l E B U V → (Integral l E U.left ⥤ Integral l E V.left)
  | .pull f _ _ _ => integralDerivedPullback l E f.left
  | .push f _ => GeneratorReduction.integralPush l E o f.left
  | .open j hj _ => letI := hj; ringedOpen l E j.left
  | .tensorLeft W N => (Functor.curry.obj (integralCompletedTensor l E W.left)).flip.obj N
  | .tensorRight W M => (Functor.curry.obj (integralCompletedTensor l E W.left)).obj M

/-- The source L A R of the specified single-operation comparison.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.source (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) :=
  (calculus l E U.left).reduction ⋙ A.system l E o ⋙ coefficientSequenceLimit l E V.left

/-- The fixed termwise, adjunction-mate, or signed tensor system shift.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.systemShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (M : System l E U.left) →
      (A.system l E o).obj (M⟦r⟧) ≅ ((A.system l E o).obj M)⟦r⟧
  | .pull f _ _ _, r, M =>
      (Functor.commShiftIso _ (self := systemPullShift l E f.left) r).app M
  | .push f _, r, M =>
      (Functor.commShiftIso _ (self := systemPushShift l E o.system f.left) r).app M
  | .open j hj _, r, M => letI := hj
      (Functor.commShiftIso _ (self := systemOpenShift l E o.system j.left) r).app M
  | .tensorLeft W N, r, M =>
      ((tensorShifts l E).systemLeft W.left r).app
        (M, (calculus l E W.left).reduction.obj N)
  | .tensorRight W M, r, N =>
      ((tensorShifts l E).systemRight W.left r).app
        ((calculus l E W.left).reduction.obj M, N)

/-- Proper image uses the composite shift of its defining L S R tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
@[instance_reducible]
def basicIntegralPushShift (o : GeneratorReduction.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (GeneratorReduction.integralPush l E o f).CommShift ℤ := by
  letI := reductionShift l E X
  letI := systemPushShift l E o.system f
  letI := limitShift l E Y
  change ((calculus l E X).reduction ⋙ Operations.push l E o.system f ⋙
    coefficientSequenceLimit l E Y).CommShift ℤ
  infer_instance

/-- The fixed integral comparison, with coefficient 1 on left tensor summands and
(-1)^(ri) on right tensor summands, followed by the specified Roos cone shift.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.integralShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (K : Integral l E U.left) →
      (A.integral l E o).obj (K⟦r⟧) ≅ ((A.integral l E o).obj K)⟦r⟧
  | .pull f _ _ _, r, K =>
      (Functor.commShiftIso _ (self := (integralShifts l E).pull f.left) r).app K
  | .push f _, r, K =>
      (Functor.commShiftIso _ (self := basicIntegralPushShift l E o f.left) r).app K
  | .open j hj _, r, K => letI := hj
      (Functor.commShiftIso _ (self := (integralShifts l E).shriek j.left) r).app K
  | .tensorLeft W N, r, K => ((tensorShifts l E).integralLeft W.left r).app (K, N)
  | .tensorRight W M, r, K => ((tensorShifts l E).integralRight W.left r).app (M, K)

/-- The source shift uses reduction, the selected operation slot, then actual total limit.
The latter is the product/cone comparison of limitShift_roos, not a chosen endpoint iso.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.sourceShift (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) (r : ℤ) (K : Integral l E U.left) :
    (A.source l E o).obj (K⟦r⟧) ≅ ((A.source l E o).obj K)⟦r⟧ :=
  (coefficientSequenceLimit l E V.left).mapIso
    ((A.system l E o).mapIso
      ((Functor.commShiftIso _ (self := reductionShift l E U.left) r).app K) ≪≫
      A.systemShift l E o r ((calculus l E U.left).reduction.obj K)) ≪≫
    (Functor.commShiftIso _ (self := limitShift l E V.left) r).app
      ((A.system l E o).obj ((calculus l E U.left).reduction.obj K))

/-- Exactly d_A from the recorded generator statement. The open map is L(r_j inverse)
followed by the inverse reconstruction unit; the proper map is identity on its tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.comparison (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (K : Integral l E U.left) →
      (A.source l E o).obj K ⟶ (A.integral l E o).obj K
  | .pull f _ _ _, K => (GeneratorReduction.pullD l E f.left).hom.app K
  | .push _ _, _ => 𝟙 _
  | .open j hj _, K => letI := hj; GeneratorReduction.openD l E o j.left K
  | .tensorLeft W N, K => (GeneratorReduction.tensorD l E W.left).hom.app (K, N)
  | .tensorRight W M, K => (GeneratorReduction.tensorD l E W.left).hom.app (M, K)

/-- Common bounds on all inputs and intermediate systems. The other tensor input
has its own completeness, compatible origin, constructibility and finite-Tor witnesses.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.admissible (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) (K : Integral l E U.left)
    (lo hi torLo torHi : ℤ) : Prop :=
  GeneratorReduction.Admissible l E (calculus l E U.left) K lo hi torLo torHi ∧
  GeneratorReduction.SystemAdmissible l E V.left
    ((A.system l E o).obj ((calculus l E U.left).reduction.obj K)) lo hi torLo torHi ∧
  match A with
  | .tensorLeft W N | .tensorRight W N =>
      GeneratorReduction.Admissible l E (calculus l E W.left) N lo hi torLo torHi
  | .pull _ _ _ _ | .push _ _ | .open _ _ _ => True

/-- Express naturality, zero-shift normalization, and addition coherence using Mathlib's
existing CommShift structure, with every component pinned to the specified comparisons.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftCoherent {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {D : Type v'} [Category.{w'} D] [HasShift D ℤ] (F : C ⥤ D)
    (σ : ∀ (r : ℤ) (X : C), F.obj (X⟦r⟧) ≅ (F.obj X)⟦r⟧) : Prop :=
  ∃ s : F.CommShift ℤ, ∀ (r : ℤ) (X : C),
    (Functor.commShiftIso F (self := s) r).app X = σ r X

/-- Shift compatibility for each specified single-operation reduction-tower realization.
Source: main-20261015, fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-pur-integral-basic-operation-shift).

Proof:
1. Use the simultaneous ringed-diagram models of
lem-sf-integral-compactification-system-realization. Exact inverse image and open
extension commute termwise with signed reindexing. Shift preserves K-injectives
(lem-weil-pbc-kinjective-shift); the direct-image comparison is also the mate fixed
by its derived unit and counit (lem-weil-pbc-derived-adjunction-shift).
2. On K-flat tensor representatives use t_(a,b), with coefficient (-1)^(bi).
Thus the first slot has coefficient 1 and the second slot has (-1)^(ri).
lem-pur-shifted-tensor-morphism-calculus gives naturality and associativity;
lem-sf-completed-tensor-shift-right gives the same quotient-compatible right formula.
The first-slot identity also commutes with all quotient transitions.
3. Reduction uses the termwise scalar-extension shift, equivalently its mate
through the actual reconstruction adjunction. For total limit, use the product
shift and send the cone coordinates (b,a) to (b,(-1)^r a). Strict transitions give
naturality; multiplying these signs gives addition coherence, including negative shifts.
4. Substitute exactly the generator node's d_A. Its pullback and tensor maps are
the fixed quotient/Roos identifications; its proper map is identity on L S R.
For open extension, openD is L of the inverse coefficient map followed by the
inverse reconstruction unit. That unit has level composites the actual reduction
maps by lem-coef-derived-system-evaluation-calculus, hence cone coordinates
(reduction maps,0), which the cone shift fixes. Each finite-level square commutes.
5. Apply the functorial Roos total cone, as in
lem-weil-pbc-ringed-strict-tower-homotopy-limit. The target integral operations use
the same quotient towers, products and cone normalization (def-pur-integral-derived-operations,
def-weil-derived-direct-image); so this gives equality of the actual derived maps,
without detecting equality by level evaluations.
6. All component maps are natural. Paste their squares under composition and
whiskering (lem-weil-pbc-commshift-nattrans-comp-whisker). The sign factors multiply
for sums of shifts and invert for negative shifts. Shift reindexes the finite common
cohomological and Tor intervals, preserves completeness, normalization, constructibility
and compatible origins, and thus stays in the stated domain with translated bounds. -/
theorem integralBasicOperationShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : GeneratorReduction.Operations l E)
    {U V : Over (Spec (.of D.k))}
    (_hUt : LocallyOfFiniteType U.hom) (_hUq : QuasiCompact U.hom)
    (_hVt : LocallyOfFiniteType V.hom) (_hVq : QuasiCompact V.hom)
    (A : BasicShiftOperation l E _ U V) :
    BasicShiftCoherent (A.system l E o) (A.systemShift l E o) ∧
    BasicShiftCoherent (A.integral l E o) (A.integralShift l E o) ∧
    BasicShiftCoherent (A.source l E o) (A.sourceShift l E o) ∧
    (∀ (K : Integral l E U.left) (lo hi torLo torHi : ℤ),
      A.admissible l E o K lo hi torLo torHi → ∀ r : ℤ,
        A.comparison l E o (K⟦r⟧) ≫ (A.integralShift l E o r K).hom =
          (A.sourceShift l E o r K).hom ≫ (A.comparison l E o K)⟦r⟧') ∧
    (∀ (K L : Integral l E U.left) (f : K ⟶ L) (lo hi torLo torHi : ℤ),
      A.admissible l E o K lo hi torLo torHi →
      A.admissible l E o L lo hi torLo torHi →
      (A.source l E o).map f ≫ A.comparison l E o L =
        A.comparison l E o K ≫ (A.integral l E o).map f) := by
  sorry

end WeilConjectures.IntegralSystemRealization
