/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralRealizationRecursion
public import WeilConjectures.SixFunctors.IntegralOperationShiftData
public import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.GeneratorReductionStatement
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.PurReductionLimitShiftAdjunction
import WeilConjectures.SixFunctors.IntegralBasicOperationShift
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shift squares for the actual normalized adjunction insertions

Source: blueprint, sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
coefficient-comparison sentence, and the agent-written six-step insertion calculation
(blueprint: lem-pur-realization-adjunction-insertion-shift).

The maps are the published Recursion maps. In particular the tensor comparison uses
both actual counits, and its second-slot shift retains the prescribed Koszul sign.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w v' w' v'' w''
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Compose designated shift comparisons, first mapping the inner comparison and
then using the outer comparison. These are actual composites, with no chosen endpoint map.
Source: blueprint coefficient-comparison sentence, insertion calculation step 1
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
def insertionCompositeShift {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {D : Type v'} [Category.{w'} D] [HasShift D ℤ]
    {T : Type v''} [Category.{w''} T] [HasShift T ℤ]
    (F : C ⥤ D) (G : D ⥤ T)
    (σ : ∀ (r : ℤ) (M : C), F.obj (M⟦r⟧) ≅ (F.obj M)⟦r⟧)
    (τ : ∀ (r : ℤ) (N : D), G.obj (N⟦r⟧) ≅ (G.obj N)⟦r⟧)
    (r : ℤ) (M : C) : (F ⋙ G).obj (M⟦r⟧) ≅ ((F ⋙ G).obj M)⟦r⟧ :=
  G.mapIso (σ r M) ≪≫ τ r (F.obj M)

/-- All clauses of a normalized insertion square on its stated input domain.
The existential CommShift structures must have exactly the displayed components;
thus zero and addition coherence refer to the fixed comparisons, including negative shifts.
Naturality is asserted for the insertion itself, not just its finite evaluations.
Source: blueprint coefficient-comparison sentence, insertion steps 2--6
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
def InsertionShiftLaw {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {D : Type v'} [Category.{w'} D] [HasShift D ℤ]
    (F G : C ⥤ D)
    (σ : ∀ (r : ℤ) (M : C), F.obj (M⟦r⟧) ≅ (F.obj M)⟦r⟧)
    (τ : ∀ (r : ℤ) (M : C), G.obj (M⟦r⟧) ≅ (G.obj M)⟦r⟧)
    (a : ∀ M : C, F.obj M ⟶ G.obj M) (P : C → Prop) : Prop :=
  (∃ s : F.CommShift ℤ, ∀ (r : ℤ) (M : C),
    (Functor.commShiftIso F (self := s) r).app M = σ r M) ∧
  (∃ s : G.CommShift ℤ, ∀ (r : ℤ) (M : C),
    (Functor.commShiftIso G (self := s) r).app M = τ r M) ∧
  (∀ M : C, P M → IsIso (a M) ∧ ∀ r : ℤ,
    a (M⟦r⟧) ≫ (τ r M).hom = (σ r M).hom ≫ (a M)⟦r⟧') ∧
  (∀ (M N : C) (f : M ⟶ N), P M → P N → F.map f ≫ a N = a M ≫ G.map f)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The fixed total-limit component, including its representative-normalized Roos cone.
Source: blueprint coefficient-comparison sentence; def-pur-integral-operation-shift-data
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
def insertionLimitShift (W : Scheme.{u}) (r : ℤ) (M : System l E W) :=
  (Functor.commShiftIso _ (self := limitShift l E W) r).app M

/-- The source square for L A uses A's designated slot, followed by the fixed total limit.
Source: blueprint coefficient-comparison sentence, insertion steps 3--4
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
def insertionSourceShift {X Y : Scheme.{u}} (A : System l E X ⥤ System l E Y)
    (σ : ∀ (r : ℤ) (M : System l E X), A.obj (M⟦r⟧) ≅ (A.obj M)⟦r⟧) :=
  insertionCompositeShift A (coefficientSequenceLimit l E Y) σ (insertionLimitShift l E Y)

/-- The target square for A_int L first uses total limit, then the same designated slot.
Source: blueprint coefficient-comparison sentence, insertion steps 3--4
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
def insertionTargetShift {X Y : Scheme.{u}} (A : Integral l E X ⥤ Integral l E Y)
    (σ : ∀ (r : ℤ) (K : Integral l E X), A.obj (K⟦r⟧) ≅ (A.obj K)⟦r⟧) :=
  insertionCompositeShift (coefficientSequenceLimit l E X) A (insertionLimitShift l E X) σ

/-- The inverse-unit and unary insertion laws, and the two separate tensor-slot laws.
All domains use the published normalization, compatible origins, constructibility and
common cohomological/Tor bounds. The maps themselves are the actual counit insertions.
Source: blueprint coefficient-comparison sentence, insertion calculation steps 1--6
(blueprint: lem-pur-realization-adjunction-insertion-shift). -/
structure RealizationAdjunctionInsertionShift (D : FiniteFieldDatum.{u})
    (o : Operations l E) (c : Realizations l E D o) : Prop where
  unit : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      ((calculus l E W.left).reduction ⋙ coefficientSequenceLimit l E W.left)
      (𝟭 (Integral l E W.left))
      (insertionCompositeShift (calculus l E W.left).reduction
        (coefficientSequenceLimit l E W.left)
        (fun r K ↦ (Functor.commShiftIso _ (self := reductionShift l E W.left) r).app K)
        (insertionLimitShift l E W.left))
      (fun _ _ ↦ Iso.refl _)
      (fun K ↦ GeneratorReduction.inverseOrZero ((calculus l E W.left).adjunction.unit.app K))
      (fun K ↦ sfIntegralConstructible l E W.left K ∧
        GeneratorReduction.SystemAdmissible l E W.left
          ((calculus l E W.left).reduction.obj K) lo hi torLo torHi)
  pull : ∀ {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      (IntegralSystemRealization.pull l E f.left ⋙ coefficientSequenceLimit l E X.left)
      (coefficientSequenceLimit l E Y.left ⋙ integralDerivedPullback l E f.left)
      (insertionSourceShift l E (IntegralSystemRealization.pull l E f.left)
        (fun r M ↦ (Functor.commShiftIso _ (self := systemPullShift l E f.left) r).app M))
      (insertionTargetShift l E (integralDerivedPullback l E f.left)
        (fun r K ↦ (Functor.commShiftIso _
          (self := (integralShifts l E).pull f.left) r).app K))
      (Recursion.pullA l E f.left)
      (fun M ↦ GeneratorReduction.SystemAdmissible l E Y.left M lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E X.left
          ((IntegralSystemRealization.pull l E f.left).obj M) lo hi torLo torHi)
  proper : ∀ {X Y : Over (Spec (.of D.k))} (p : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsProper p.left]
    (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      (Operations.push l E o p.left ⋙ coefficientSequenceLimit l E Y.left)
      (coefficientSequenceLimit l E X.left ⋙
        PurCompactSupport.push (PurCompactSupport.completed l E) p.left)
      (insertionSourceShift l E (Operations.push l E o p.left)
        (fun r M ↦ (Functor.commShiftIso _ (self := systemPushShift l E o p.left) r).app M))
      (insertionTargetShift l E
        (PurCompactSupport.push (PurCompactSupport.completed l E) p.left)
        (fun r K ↦ (Functor.commShiftIso _
          (self := (integralShifts l E).push p.left) r).app K))
      (Recursion.properA l E c p.left)
      (fun M ↦ GeneratorReduction.SystemAdmissible l E X.left M lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E Y.left
          ((Operations.push l E o p.left).obj M) lo hi torLo torHi)
  openExtension : ∀ {X Y : Over (Spec (.of D.k))} (j : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsOpenImmersion j.left] [QuasiCompact j.left] (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      (Operations.shriek l E o j.left ⋙ coefficientSequenceLimit l E Y.left)
      (coefficientSequenceLimit l E X.left ⋙ ringedOpen l E j.left)
      (insertionSourceShift l E (Operations.shriek l E o j.left)
        (fun r M ↦ (Functor.commShiftIso _ (self := systemOpenShift l E o j.left) r).app M))
      (insertionTargetShift l E (ringedOpen l E j.left)
        (fun r K ↦ (Functor.commShiftIso _
          (self := (integralShifts l E).shriek j.left) r).app K))
      (Recursion.openA l E c j.left)
      (fun M ↦ GeneratorReduction.SystemAdmissible l E X.left M lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E Y.left
          ((Operations.shriek l E o j.left).obj M) lo hi torLo torHi)
  tensorLeft : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (N : System l E W.left) (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj N ⋙
        coefficientSequenceLimit l E W.left)
      (coefficientSequenceLimit l E W.left ⋙
        (Functor.curry.obj (integralCompletedTensor l E W.left)).flip.obj
          ((coefficientSequenceLimit l E W.left).obj N))
      (insertionSourceShift l E
        ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj N)
        (fun r M ↦ ((tensorShifts l E).systemLeft W.left r).app (M, N)))
      (insertionTargetShift l E
        ((Functor.curry.obj (integralCompletedTensor l E W.left)).flip.obj
          ((coefficientSequenceLimit l E W.left).obj N))
        (fun r K ↦ ((tensorShifts l E).integralLeft W.left r).app
          (K, (coefficientSequenceLimit l E W.left).obj N)))
      (fun M ↦ Recursion.tensorA l E W.left M N)
      (fun M ↦ GeneratorReduction.SystemAdmissible l E W.left M lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E W.left N lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E W.left
          ((calculus l E W.left).systemClosed.tensor.obj (M, N)) lo hi torLo torHi)
  tensorRight : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (M : System l E W.left) (lo hi torLo torHi : ℤ),
    InsertionShiftLaw
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj M ⋙
        coefficientSequenceLimit l E W.left)
      (coefficientSequenceLimit l E W.left ⋙
        (Functor.curry.obj (integralCompletedTensor l E W.left)).obj
          ((coefficientSequenceLimit l E W.left).obj M))
      (insertionSourceShift l E
        ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj M)
        (fun r N ↦ ((tensorShifts l E).systemRight W.left r).app (M, N)))
      (insertionTargetShift l E
        ((Functor.curry.obj (integralCompletedTensor l E W.left)).obj
          ((coefficientSequenceLimit l E W.left).obj M))
        (fun r K ↦ ((tensorShifts l E).integralRight W.left r).app
          ((coefficientSequenceLimit l E W.left).obj M, K)))
      (Recursion.tensorA l E W.left M)
      (fun N ↦ GeneratorReduction.SystemAdmissible l E W.left M lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E W.left N lo hi torLo torHi ∧
        GeneratorReduction.SystemAdmissible l E W.left
          ((calculus l E W.left).systemClosed.tensor.obj (M, N)) lo hi torLo torHi)

/-- The inverse unit and the actual unary and two-slot tensor counit insertions
commute naturally with every integer shift, coherently for zero and addition.
Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
coefficient-comparison sentence; the agent-written insertion calculation
(blueprint: lem-pur-realization-adjunction-insertion-shift).

Proof:
1. Integral realization recursion gives invertible actual u and e on the common-bound
normalized domain, and identifies the maps with the displayed inverse-counit insertions.
2. The reduction/limit shift-adjunction theorem gives the square for the actual unit.
Invert its two unit components to get the square for u inverse, keeping the Roos shift.
3. For a unary A set b=L A(e) and h=d_A L. Whisker the counit square by L A;
prewhisker the basic-operation square by L and use naturality at the L-shift.
Thus both b and h commute with the composite fixed comparisons.
4. For tensor factor e_M tensor e_N in the order appropriate to the designated slot.
Use the counit square in that slot and tensor-shift naturality at the other counit.
Apply L and its shift. Precompose the signed basic-operation square with L in that slot.
The second-slot Koszul coefficient remains (-1)^(ri), since the counits have degree zero.
5. Invert the b square and paste with the h square: a=b inverse followed by h.
The same inversion and composition of naturality equations proves naturality of a.
6. Basic-operation shifts are coherent. Apply adjunction-shift uniqueness to the
opposite adjunction L^op -| R^op to identify the reduction mate with the cochain shift.
Composition, inversion and whiskering preserve the squares. The tensor signs multiply
as (-1)^(ri)(-1)^(si)=(-1)^((r+s)i); the cone diagonals (1,(-1)^r) multiply in the same way.
Hence the fixed comparisons satisfy zero and addition coherence for all integers.
Shift translates the finite cohomological and Tor bounds by -r. Zero objects and empty
opens give their unique maps, and r=0 gives the identity square. -/
theorem realizationAdjunctionInsertionShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (c : Realizations l E D o) :
    RealizationAdjunctionInsertionShift l E D o c := by
  sorry

end WeilConjectures.IntegralSystemRealization
