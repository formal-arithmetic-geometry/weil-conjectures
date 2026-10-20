/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.SixFunctors.IntegralExpressionOccurrences
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.SixFunctors.CompletedTensorShiftRight
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Representative-normalized shifts for integral realization operations

Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2;
cochain tensor and mapping-cone conventions of Stacks 011G, 014E and 0941
(blueprint: def-pur-integral-operation-shift-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.IntegralSystemRealization

/-- Shift only the first operand of a bifunctor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def tensorShiftFirst (A : Type v) [Category.{w} A] [HasShift A ℤ] (r : ℤ) :
    A × A ⥤ A × A := (shiftFunctor A r).prod (𝟭 A)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual total tensor on complexes of strict systems.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemTotalTensor (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

/-- K-flatness on the actual sequence site.
Source: Stacks 06YN (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemKFlat (W : Scheme.{u})
    (P : CochainComplex (coefficientSequenceModules l E W) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf l E W) P

/-- The unsigned first-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i + r)).val.obj U) (y : (Q.X (j)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P⟦r⟧) (Q) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i + r) + (j)) (by omega)).inv.val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i + r) (j)
          ((i + r) + (j)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (P⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorLeftFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj (P⟦r⟧), DerivedCategory.Q.obj Q))
        (Y := ((DerivedCategory.Q.obj P)⟦r⟧, DerivedCategory.Q.obj Q))
        (((DerivedCategory.Q.commShiftIso r).hom.app P), 𝟙 (DerivedCategory.Q.obj Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P⟦r⟧) (Q) hS hQ).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The signed second-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i)).val.obj U) (y : (Q.X (j + r)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P) (Q⟦r⟧) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i) + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i) (j + r)
          ((i) + (j + r)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightProperty (W : Scheme.{u}) (r : ℤ)
    (σ : completedTensorShiftSecond (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (Q⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorRightFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦r⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦r⟧))
        (𝟙 (DerivedCategory.Q.obj P), ((DerivedCategory.Q.commShiftIso r).hom.app Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P) (Q⟦r⟧) hP hS).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The first-slot finite tensor formula, before the fixed product/cone passage.
Source: Stacks 011G (blueprint: def-pur-integral-operation-shift-data). -/
def integralTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (i + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X j).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) ((i + r) + j) (by omega)).inv.val.app U)
      (integralOperationsTotalTensorSection l E W n P Q (i + r) j U x y)

/-- First-slot descent through exactly the recorded finite tower and Roos cone.
Source: Stacks 014E, 0941 (blueprint: def-pur-integral-operation-shift-data). -/
def integralTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ (hP : integralOperationsGoodComplex l E W (P.obj⟦r⟧))
      (α : (integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      integralTensorLeftFormula l E W P.obj Q.obj r α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r α δ ∧
        (integralCompletedTensor l E W).map
            (((DerivedCategory.Q.commShiftIso r).hom.app P.obj),
              𝟙 (DerivedCategory.Q.obj Q.obj)) ≫
          σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (shiftFunctor (Integral l E W) r).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) =
        (integralCompletedTensorComparison l E W).hom.app (⟨P.obj⟦r⟧, hP⟩, Q) ≫
          DerivedCategory.Q.map
            (completedTensorShiftRoosIso
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r δ).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))

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
  sorry

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

/-- Shift comparisons for each primitive operation; tensor slots remain separate.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure InterpretationShifts {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] (d : Interpretation C) where
  pull {U V : Scheme.{u}} (f : U ⟶ V) : (d.pull f).CommShift ℤ
  push {U V : Scheme.{u}} (f : U ⟶ V) : (d.push f).CommShift ℤ
  shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] : (d.shriek j).CommShift ℤ
  compactSupport {U V : Scheme.{u}} (f : U ⟶ V) (c : Compactification f) :
    (d.compactSupport f c).CommShift ℤ
  tensorLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (C W) r ⋙ d.tensor W ≅ d.tensor W ⋙ shiftFunctor (C W) r
  tensorRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (C W) r ⋙ d.tensor W ≅
      d.tensor W ⋙ shiftFunctor (C W) r

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

/-- Reindex shifts through the actual single-slot context, with the designated
left or right tensor comparison at every tensor vertex.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def Expression.SlotContext.shift {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ] {d : Interpretation C}
    (a : InterpretationShifts d) {A : Over B} (r : ℤ) :
    {W : Over B} → (e : Expression.SlotContext d A W) → (P : C A.left) →
      e.evaluate.obj (P⟦r⟧) ≅ (e.evaluate.obj P)⟦r⟧
  | _, .input, _ => Iso.refl _
  | _, .pull f e, P => (d.pull f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r).app (e.evaluate.obj P)
  | _, .push f _ e, P => (d.push f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r).app (e.evaluate.obj P)
  | _, .shriek j hj _ e, P =>
    letI := hj
    (d.shriek j.left).mapIso (e.shift a r P) ≪≫
      (Functor.commShiftIso (d.shriek j.left) (self := a.shriek j.left) r).app
        (e.evaluate.obj P)
  | _, .compactSupport f c e, P => (d.compactSupport f.left c).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.compactSupport f.left c)
      (self := a.compactSupport f.left c) r).app (e.evaluate.obj P)
  | W, .tensorLeft e N, P =>
    ((Functor.curry.obj (d.tensor W.left)).flip.obj N).mapIso (e.shift a r P) ≪≫
      (a.tensorLeft W.left r).app (e.evaluate.obj P, N)
  | W, .tensorRight M e, P =>
    ((Functor.curry.obj (d.tensor W.left)).obj M).mapIso (e.shift a r P) ≪≫
      (a.tensorRight W.left r).app (M, e.evaluate.obj P)

open Classical in
/-- The actual comparison for a single independently labelled input.
Its endpoint identifications are equalities of explicit evaluations, not chosen isos.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.shift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate d).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate d).obj K)⟦r⟧ :=
  (eqToIso (e.variableContext_evaluate d K i ((K i)⟦r⟧)).1).symm ≪≫
    (e.variableContext d K i).shift a r (K i) ≪≫
    (shiftFunctor (C W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate d K i (K i)).2)

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
  sorry

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

/-- Both expression shift comparisons are natural in every input, including the
unselected operands of a tensor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data).

Proof: induct on the unique selected path. The variable case is the natural shift
of reduction, or identity integrally. At unary vertices use naturality of the
primitive functor's shift and its functorial image of the induction equality.
At tensor vertices use naturality in both operands of the representative-normalized
left or right tensor isomorphism. The other subtree's map is its actual evaluation
on the input-family morphism. Naturality of total limit's shift finishes the source.
The endpoint equalities are the dependent-update identities, so equality transport
preserves each equation. This proves both displayed naturality squares. -/
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
        ((e.val.evaluate (integralInterpretation l E)).map f)⟦r⟧' := by
  sorry

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



