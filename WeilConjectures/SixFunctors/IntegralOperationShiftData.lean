/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralTensorShiftProperties
public import WeilConjectures.SixFunctors.IntegralExpressionOccurrences
public import WeilConjectures.SixFunctors.IndependentExpressionShiftNaturality
public import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
public import WeilConjectures.AlgebraicGeometry.IntegralComparisonRealizationModels
public import WeilConjectures.SixFunctors.CompletedTensorShiftRight
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

public import WeilConjectures.SixFunctors.IndependentExpressionReductionShift
import WeilConjectures.SixFunctors.SystemTensorLeftShiftUnique
import WeilConjectures.SixFunctors.SystemTensorRightShiftUnique
import WeilConjectures.SixFunctors.IntegralTensorLeftShiftUnique
import WeilConjectures.SixFunctors.IntegralTensorRightShiftUnique

/-! # Representative-normalized shifts for integral realization operations

Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2;
cochain tensor and mapping-cone conventions of Stacks 011G, 014E and 0941
(blueprint: def-pur-integral-operation-shift-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Both tensor slots, with the actual K-flat and Roos normalizations.
No endpoint isomorphism is accepted without its representative characterization.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure TensorShifts where
  systemLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r
  systemLeft_normalized (W : Scheme.{u}) (r : ℤ) :
    systemTensorLeftProperty l E W r (systemLeft W r)
  systemRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r
  systemRight_normalized (W : Scheme.{u}) (r : ℤ) :
    systemTensorRightProperty l E W r (systemRight W r)
  integralLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r
  integralLeft_normalized (W : Scheme.{u}) (r : ℤ) :
    integralTensorLeftProperty l E W r (integralLeft W r)
  integralRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r
  integralRight_normalized (W : Scheme.{u}) (r : ℤ) :
    integralCompletedTensorRightShiftProperty l E W r (integralRight W r)

private theorem tensorShifts_ext (s t : TensorShifts l E)
    (hsl : s.systemLeft = t.systemLeft) (hsr : s.systemRight = t.systemRight)
    (hil : s.integralLeft = t.integralLeft) (hir : s.integralRight = t.integralRight) :
    s = t := by
  cases s
  cases t
  dsimp only at hsl hsr hil hir
  cases hsl
  cases hsr
  cases hil
  cases hir
  rfl

set_option linter.unusedVariables false in
/-- The representative formulas uniquely determine the four tensor comparisons.
Source: Stacks 011G, 012Z, 014E, 06YU, 0941 and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data).

Proof: on total complexes, reindex the first slot with coefficient 1 and the
second (i,j)-summand with coefficient (-1)^(ri). The signed differentials give
chain isomorphisms, natural in both complexes. Shifts preserve K-flatness and
termwise flatness. The same maps commute with every coefficient transition.
For completed tensor pass to products and to Cone(1-s), using diagonal
coefficients (1,(-1)^r), then shift by -1. This gives exactly the two displayed
completed properties. The K-flat model comparisons descend the strict-system
maps, giving their displayed properties. Every object has the recorded resolving
representatives. Total tensor generators and the two cone summands determine
the cochain maps, while localization determines their derived maps on all roofs.
Thus each natural comparison is unique. Proof irrelevance identifies all the
normalization witnesses, and extensionality identifies the four families. -/
theorem tensorShifts_existsUnique : ∃! s : TensorShifts l E, True := by
  classical
  let sl := fun W r ↦ (systemTensorLeftShift_existsUnique l E W r).exists.choose
  let sr := fun W r ↦ (systemTensorRightShift_existsUnique l E W r).exists.choose
  let il := fun W r ↦ (integralTensorLeftShift_existsUnique l E W r).exists.choose
  let ir := fun W r ↦ (integralTensorRightShift_existsUnique l E W r).exists.choose
  let s : TensorShifts l E :=
    { systemLeft := sl
      systemLeft_normalized := fun W r ↦
        (systemTensorLeftShift_existsUnique l E W r).exists.choose_spec
      systemRight := sr
      systemRight_normalized := fun W r ↦
        (systemTensorRightShift_existsUnique l E W r).exists.choose_spec
      integralLeft := il
      integralLeft_normalized := fun W r ↦
        (integralTensorLeftShift_existsUnique l E W r).exists.choose_spec
      integralRight := ir
      integralRight_normalized := fun W r ↦
        (integralTensorRightShift_existsUnique l E W r).exists.choose_spec }
  refine ⟨s, trivial, ?_⟩
  intro t _
  have hsl : t.systemLeft = s.systemLeft := by
    funext W r
    exact (systemTensorLeftShift_existsUnique l E W r).unique
      (t.systemLeft_normalized W r) (s.systemLeft_normalized W r)
  have hsr : t.systemRight = s.systemRight := by
    funext W r
    exact (systemTensorRightShift_existsUnique l E W r).unique
      (t.systemRight_normalized W r) (s.systemRight_normalized W r)
  have hil : t.integralLeft = s.integralLeft := by
    funext W r
    exact (integralTensorLeftShift_existsUnique l E W r).unique
      (t.integralLeft_normalized W r) (s.integralLeft_normalized W r)
  have hir : t.integralRight = s.integralRight := by
    funext W r
    exact (integralTensorRightShift_existsUnique l E W r).unique
      (t.integralRight_normalized W r) (s.integralRight_normalized W r)
  exact tensorShifts_ext l E t s hsl hsr hil hir

/-- The tensor shifts chosen from a characterization that determines every map.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def tensorShifts : TensorShifts l E := (tensorShifts_existsUnique l E).exists.choose

/-- Canonical exact-restriction/right-derived-limit shift, with unchanged universes.
Source: Stacks 0941 (blueprint: def-pur-integral-operation-shift-data). -/
@[instance_reducible]
def limitShift (W : Scheme.{u}) : (coefficientSequenceLimit l E W).CommShift ℤ := by
  dsimp [coefficientSequenceLimit, coefficientSequenceDerivedRestriction,
    coefficientConstantTowerLimit]
  infer_instance

/-- The reduction shift is the mate through the actual reconstruction adjunction.
Source: Stacks 06YY, 0941 (blueprint: def-pur-integral-operation-shift-data). -/
@[instance_reducible]
def reductionShift (W : Scheme.{u}) : ((calculus l E W).reduction).CommShift ℤ :=
  letI := limitShift l E W
  (calculus l E W).adjunction.leftAdjointCommShift ℤ

/-- Exact inverse image has its localized termwise cochain shift.
Source: Stacks 03D2 (blueprint: def-pur-integral-operation-shift-data). -/
@[instance_reducible]
def systemPullShift {U V : Scheme.{u}} (f : U ⟶ V) : (pull l E f).CommShift ℤ := by
  dsimp [pull, pullbackTensorSequenceDerived]
  infer_instance

/-- Direct image has the mate of that shift through its specified derived adjunction.
Source: Stacks 07A5 (blueprint: def-pur-integral-operation-shift-data). -/
@[instance_reducible]
def systemPushShift (o : Operations l E) {U V : Scheme.{u}} (f : U ⟶ V) :
    (Operations.push l E o f).CommShift ℤ :=
  letI := systemPullShift l E f
  (o.direct f).adj.rightAdjointCommShift ℤ

/-- Exact open extension has the localized termwise shift.
Source: Stacks 03DI (blueprint: def-pur-integral-operation-shift-data). -/
@[instance_reducible]
def systemOpenShift (o : Operations l E) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] : (Operations.shriek l E o j).CommShift ℤ := by
  dsimp [Operations.shriek, Open.derived]
  infer_instance

/-- The fixed shifts on strict-system operations and their actual composites.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def systemShifts (o : Operations l E) : InterpretationShifts (systemInterpretation l E o) where
  pull := systemPullShift l E
  push := systemPushShift l E o
  shriek := systemOpenShift l E o
  compactSupport _f c := by
    letI := systemOpenShift l E o c.i
    letI := systemPushShift l E o c.g
    change (Operations.shriek l E o c.i ⋙ Operations.push l E o c.g).CommShift ℤ
    infer_instance
  tensorLeft := (tensorShifts l E).systemLeft
  tensorRight := (tensorShifts l E).systemRight

/-- The fixed integral shifts: completed pullback uses its signed Roos descent;
proper image and open extension use right derivation and exact localization.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def integralShifts : InterpretationShifts (integralInterpretation l E) where
  pull := fieldIntegralPullShift l E
  push f := by
    dsimp [integralInterpretation, PurCompactSupport.push, proEtaleRingDerivedDirectImage]
    infer_instance
  shriek j := by
    dsimp [integralInterpretation]
    infer_instance
  compactSupport f c := by
    dsimp [integralInterpretation, PurCompactSupport.image, proEtaleRingDerivedDirectImage]
    infer_instance
  tensorLeft := (tensorShifts l E).integralLeft
  tensorRight := (tensorShifts l E).integralRight

/-- The ambient source of the recorded realization, with independent input labels.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.source {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W) :
    (∀ i, Integral l E (X i).left) ⥤ Integral l E W.left :=
  inputReduction l E X ⋙ e.val.evaluate (systemInterpretation l E o) ⋙
    coefficientSequenceLimit l E W.left

open Classical in
/-- Reduction commutes with replacement of an independently labelled input.
This equality involves the actual reduction functor, not a selected representative.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data).

Proof: the inputReduction functor is pointwise reduction. At the selected index
its updated value is reduction of P, and at all other indices it is unchanged.
The independent-context evaluation identity therefore gives the claimed equality. -/
theorem IndependentExpression.reductionContext_evaluate {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} (o : Operations l E) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, Integral l E (X i).left)
    (i : I) (P : Integral l E (X i).left) :
    ((e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i).evaluate).obj
        ((calculus l E (X i).left).reduction.obj P) =
      (e.val.evaluate (systemInterpretation l E o)).obj
        ((inputReduction l E X).obj (Function.update K i P)) := by
  rw [(e.variableContext_evaluate (systemInterpretation l E o)
    ((inputReduction l E X).obj K) i
    ((calculus l E (X i).left).reduction.obj P)).1]
  apply congrArg (e.val.evaluate (systemInterpretation l E o)).obj
  funext j
  by_cases h : j = i
  · subst j
    simp [inputReduction]
  · simp [inputReduction, Function.update_of_ne h]

open Classical in
/-- Source shift: the reduction mate, the exact/proper/open/signed-tensor context,
and finally total limit's canonical shift, with their actual evaluation endpoints.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.sourceShift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ) :
    (e.source l E o).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.source l E o).obj K)⟦r⟧ :=
  let ctx := e.variableContext (systemInterpretation l E o) ((inputReduction l E X).obj K) i
  (coefficientSequenceLimit l E W.left).mapIso
    ((eqToIso (e.reductionContext_evaluate l E o K i ((K i)⟦r⟧))).symm ≪≫
      ctx.evaluate.mapIso
        ((Functor.commShiftIso ((calculus l E (X i).left).reduction)
          (self := reductionShift l E (X i).left) r).app (K i)) ≪≫
      ctx.shift (systemShifts l E o) r ((calculus l E (X i).left).reduction.obj (K i)) ≪≫
      (shiftFunctor (System l E W.left) r).mapIso
        (eqToIso (e.variableContext_evaluate (systemInterpretation l E o)
          ((inputReduction l E X).obj K) i
          ((calculus l E (X i).left).reduction.obj (K i))).2)) ≪≫
    (Functor.commShiftIso (coefficientSequenceLimit l E W.left)
      (self := limitShift l E W.left) r).app
        ((e.val.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K))

open Classical in
/-- Integral shift through the exact same independent slot and expression context.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.integralShift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate (integralInterpretation l E)).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate (integralInterpretation l E)).obj K)⟦r⟧ :=
  e.shift (integralInterpretation l E) (integralShifts l E) K i r

/-- The components for a single-input shift, on the ambient family category.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.sourceShiftComponent {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} (o : Operations l E) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, Integral l E (X i).left)
    (i : I) (r : ℤ) :
    (e.source l E o).obj ((inputShift (fun j ↦ Integral l E (X j).left) i r).obj K) ≅
      ((e.source l E o).obj K)⟦r⟧ :=
  (e.source l E o).mapIso (eqToIso (inputShift_obj _ K i r)) ≪≫
    e.sourceShift l E o K i r

/-- The corresponding components on the actual integral expression functor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.integralShiftComponent {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate (integralInterpretation l E)).obj
        ((inputShift (fun j ↦ Integral l E (X j).left) i r).obj K) ≅
      ((e.val.evaluate (integralInterpretation l E)).obj K)⟦r⟧ :=
  (e.val.evaluate (integralInterpretation l E)).mapIso
      (eqToIso (inputShift_obj _ K i r)) ≪≫ e.integralShift l E K i r

attribute [local irreducible] reductionShift limitShift systemShifts integralShifts
attribute [local irreducible] IndependentExpression.sourceShiftComponent
  IndependentExpression.integralShiftComponent

/-- The source component decomposes into pointwise reduction, expression shift,
and total-limit shift. The endpoint equalities are the explicit context
identifications from `variableContext_evaluate` and `reductionContext_evaluate`.
Source: blueprint Step 2 (blueprint: lem-pur-independent-expression-reduction-shift).
(blueprint: lem-pur-independent-expression-source-component-decomposition).

Proof: expand the source shift component. The pointwise component equation
identifies its reduction shift and endpoint transports with evaluation of the
pointwise input-shift isomorphism. The remaining factors are exactly the
recursive expression shift and total-limit shift. Functoriality and associativity
combine these equalities; proof irrelevance identifies the endpoint transports. -/
theorem IndependentExpression.sourceShiftComponent_decomposition
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B}
    (e : IndependentExpression B I X W)
    (M : ∀ j, Integral l E (X j).left) (i : I) (r : ℤ) :
    e.sourceShiftComponent l E o M i r =
      (coefficientSequenceLimit l E W.left).mapIso
        ((e.val.evaluate (systemInterpretation l E o)).mapIso
            ((pointwiseInputShiftIso (C := fun j ↦ Integral l E (X j).left)
              (D := fun j ↦ System l E (X j).left)
              (fun j ↦ (calculus l E (X j).left).reduction)
              (fun j ↦ reductionShift l E (X j).left) i r).app M) ≪≫
          (e.val.evaluate (systemInterpretation l E o)).mapIso
            (eqToIso (inputShift_obj _ ((inputReduction l E X).obj M) i r)) ≪≫
          e.shift (systemInterpretation l E o) (systemShifts l E o)
            ((inputReduction l E X).obj M) i r) ≪≫
        (Functor.commShiftIso (coefficientSequenceLimit l E W.left)
          (self := limitShift l E W.left) r).app
          ((e.val.evaluate (systemInterpretation l E o)).obj
            ((inputReduction l E X).obj M)) := by
  classical
  have h := e.pointwiseShift_component
    (fun j ↦ (calculus l E (X j).left).reduction)
    (fun j ↦ reductionShift l E (X j).left) (systemInterpretation l E o) M i r
  apply Iso.ext
  simp only [IndependentExpression.sourceShiftComponent, IndependentExpression.sourceShift,
    IndependentExpression.source, IndependentExpression.shift, Iso.trans_hom,
    Functor.mapIso_hom, Functor.comp_map, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Functor.map_comp, Category.assoc]
  have h' := congrArg (coefficientSequenceLimit l E W.left).map h
  simp only [Functor.map_comp] at h'
  erw [reassoc_of% h'.symm]
  rfl

/-- The source part of independent expression shift naturality.
Source: blueprint Step 2 (blueprint: lem-pur-independent-expression-source-naturality).

Proof: by the component decomposition each component is total limit applied to the
pointwise reduction shift, an input-shift transport and the generic expression shift,
followed by total limit's shift. Naturality of the pointwise reduction shift and the
generic expression naturality square on the reduced morphism give the square before
total limit; apply total limit and naturality of its shift. -/
theorem IndependentExpression.sourceShift_naturality
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B}
    (e : IndependentExpression B I X W) (K N : ∀ i, Integral l E (X i).left)
    (f : K ⟶ N) (i : I) (r : ℤ) :
    (e.source l E o).map ((inputShift _ i r).map f) ≫
        (e.sourceShiftComponent l E o N i r).hom =
      (e.sourceShiftComponent l E o K i r).hom ≫ ((e.source l E o).map f)⟦r⟧' := by
  let d := systemInterpretation l E o
  let L := coefficientSequenceLimit l E W.left
  let F := e.val.evaluate d
  let R := inputReduction l E X
  let χ := pointwiseInputShiftIso (C := fun j ↦ Integral l E (X j).left)
    (D := fun j ↦ System l E (X j).left)
    (fun j ↦ (calculus l E (X j).left).reduction)
    (fun j ↦ reductionShift l E (X j).left) i r
  let ι := fun M : ∀ j, Integral l E (X j).left ↦
    F.mapIso (χ.app M) ≪≫ F.mapIso (eqToIso (inputShift_obj _ (R.obj M) i r)) ≪≫
      e.shift d (systemShifts l E o) (R.obj M) i r
  have hχ : R.map ((inputShift _ i r).map f) ≫ χ.hom.app N =
      χ.hom.app K ≫ (inputShift _ i r).map (R.map f) := χ.hom.naturality f
  have hg := e.shift_naturality_generic d (systemShifts l E o) (R.obj K) (R.obj N)
    (R.map f) i r
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hg
  have key : F.map (R.map ((inputShift _ i r).map f)) ≫ (ι N).hom =
      (ι K).hom ≫ (F.map (R.map f))⟦r⟧' := by
    simp only [ι, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [← F.map_comp_assoc, hχ, F.map_comp, Category.assoc, hg]
    simp only [Category.assoc]
    rfl
  have hL : (coefficientSequenceLimit l E W.left).map
        ((shiftFunctor (System l E W.left) r).map
          ((e.val.evaluate (systemInterpretation l E o)).map ((inputReduction l E X).map f))) ≫
      ((Functor.commShiftIso (coefficientSequenceLimit l E W.left)
        (self := limitShift l E W.left) r).app
          ((e.val.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj N))).hom =
      ((Functor.commShiftIso (coefficientSequenceLimit l E W.left)
        (self := limitShift l E W.left) r).app
          ((e.val.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K))).hom ≫
        (shiftFunctor (Integral l E W.left) r).map ((e.source l E o).map f) :=
    (Functor.commShiftIso (coefficientSequenceLimit l E W.left)
      (self := limitShift l E W.left) r).hom.naturality
        ((e.val.evaluate (systemInterpretation l E o)).map ((inputReduction l E X).map f))
  rw [e.sourceShiftComponent_decomposition l E o N i r,
    e.sourceShiftComponent_decomposition l E o K i r]
  change L.map (F.map (R.map ((inputShift _ i r).map f))) ≫
      (L.mapIso (ι N) ≪≫ _).hom = (L.mapIso (ι K) ≪≫ _).hom ≫ _
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    ← L.map_comp_assoc, key, L.map_comp, Category.assoc, Category.assoc]
  rw [hL]

/-- Both expression shift comparisons are natural in every input, including the
unselected operands of a tensor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data).

The source square is supplied by sourceShift_naturality. The integral square is
proved directly by the generic independent-expression naturality theorem. -/
theorem IndependentExpression.shift_naturality {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} (o : Operations l E) {W : Over B}
    (e : IndependentExpression B I X W) (K N : ∀ i, Integral l E (X i).left)
    (f : K ⟶ N) (i : I) (r : ℤ) :
    (e.source l E o).map ((inputShift _ i r).map f) ≫
        (e.sourceShiftComponent l E o N i r).hom =
      (e.sourceShiftComponent l E o K i r).hom ≫ ((e.source l E o).map f)⟦r⟧' ∧
    (e.val.evaluate (integralInterpretation l E)).map ((inputShift _ i r).map f) ≫
        (e.integralShiftComponent l E N i r).hom =
      (e.integralShiftComponent l E K i r).hom ≫
        ((e.val.evaluate (integralInterpretation l E)).map f)⟦r⟧'  := by
  constructor
  · exact e.sourceShift_naturality l E o K N f i r
  · simpa only [IndependentExpression.integralShiftComponent,
      IndependentExpression.integralShift] using
      e.shift_naturality_generic (integralInterpretation l E) (integralShifts l E)
        K N f i r

/-- Source comparisons as natural isomorphisms of all independently supplied inputs.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.sourceShiftIso {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W)
    (i : I) (r : ℤ) :
    inputShift (fun j ↦ Integral l E (X j).left) i r ⋙ e.source l E o ≅
      e.source l E o ⋙ shiftFunctor (Integral l E W.left) r :=
  NatIso.ofComponents (fun K ↦ e.sourceShiftComponent l E o K i r)
    (fun f ↦ (e.shift_naturality l E o _ _ f i r).1)

/-- Integral comparisons as natural isomorphisms of all independently supplied inputs.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.integralShiftIso {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W)
    (i : I) (r : ℤ) :
    inputShift (fun j ↦ Integral l E (X j).left) i r ⋙
        e.val.evaluate (integralInterpretation l E) ≅
      e.val.evaluate (integralInterpretation l E) ⋙ shiftFunctor (Integral l E W.left) r :=
  NatIso.ofComponents (fun K ↦ e.integralShiftComponent l E K i r)
    (fun f ↦ (e.shift_naturality l E o _ _ f i r).2)

/-- The actual strict completed-coefficient tower underlying a system complex.
Source: Stacks 0941 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev restrictedTower (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor

/-- The exact ordinary coefficient restriction at one positive level.
Source: Stacks 0941 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev levelRestriction (W : Scheme.{u}) (n : ℕ) :=
  coefficientSequenceRestriction l E W ⋙
    (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)

/-- Canonical total limit uses the specified product and shifted-cone comparison
on every strict system representative. In particular this applies to a representative
of the actual system S_p J_j R(K) and its termwise shifted tower.
Source: Stacks 014E, 0941 and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data).

Proof: first use a simultaneous K-injective representative of the strict tower.
The right-derived shift of limit is represented by termwise cochain reindexing.
The normalized Roos bridge is the ordinary limit tuple in the product coordinate
and zero in the shifted coordinate. It commutes with product reindexing. The cone
comparison has diagonal coefficients (1,(-1)^r); on the limit tuple and zero it
therefore gives the same map. This proves the equation on simultaneous K-injectives.
Naturality of the bridge and of the given alpha transports it along a resolution
of C and D, proving it for arbitrary representatives. The specified beta equations
identify the termwise maps, and the two cone summands determine delta. Thus the
Roos isomorphism is exactly its [-1] shift, with no free cone or tower comparison. -/
/- STATEMENT-DISPUTED: the shifted-cone Roos comparison omits the factor
(-1)^r required for a coherent mapping-cocone shift. In odd degree it negates
the ordinary limit tuple, contrary to the unsigned K-injective normalization.
See SignedCoconeShift.signedCoconeShiftIso and its inl equation. -/
theorem limitShift_roos (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l E W)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ) (α : D ≅ C⟦r⟧)
    (β : restrictedTower l E W D ≅ restrictedTower l E W C ⋙
      shiftFunctor (CochainComplex (scalarReductionSource l E W) ℤ) r)
    (hβ : ∀ n : ℕ, (β.hom.app (op n)) =
      ((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).map α.hom ≫
        (((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app C)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub (restrictedTower l E W D)) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub (restrictedTower l E W C)))⟦r⟧)
    (hδ : completedTensorShiftConeFormula
      (restrictedTower l E W C) (restrictedTower l E W D) r β δ) :
    (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map α.hom) ≫
        (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app C) ≫
        (Functor.commShiftIso (coefficientSequenceLimit l E W)
          (self := limitShift l E W) r).hom.app (DerivedCategory.Q.obj C) ≫
        (shiftFunctor (Integral l E W) r).map
          (integralComparisonRoosBridge l E W ρ C).hom =
      (integralComparisonRoosBridge l E W ρ D).hom ≫
        DerivedCategory.Q.map
          (completedTensorShiftRoosIso (restrictedTower l E W C)
            (restrictedTower l E W D) r δ).hom ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (integralOperationsRoos (restrictedTower l E W C)) := by
  sorry

end WeilConjectures.IntegralSystemRealization
