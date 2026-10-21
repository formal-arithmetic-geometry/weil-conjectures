/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CommonTensorComparisonRepresentatives

/-! # Tensor comparisons through rationalization and common finite fields

Source: Weil blueprint, main-20261015, order 1826, final coefficient paragraph,
and order 1868; the conditional descent argument of the DAG
(blueprint: def-sf-common-tensor-comparison-descent).

All raw localizations and common-stage quotients below are the existing constructions.
The auxiliary records only organize the hypotheses and the normalized conclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u c h

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace WeilConjectures.TensorComparisonDescent

attribute [local semireducible] FieldOf

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

variable {l Ω}
  (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear
      (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

variable {C} {A : IntegralData C} [RationalStructures C] (R : RationalData C A)

/-- Common-stage monoidal structures on the existing source quotient and target pairs.
Source: blueprint orders 1826, 1868, DAG proof step 7
(blueprint: def-sf-common-tensor-comparison-descent). -/
class CommonStructures where
  sourceMonoidal : MonoidalCategory R.S.PairCategory
  sourceSymmetric : @SymmetricCategory R.S.PairCategory _ sourceMonoidal
  targetMonoidal : MonoidalCategory (DerivedCategory.PointFdQbar l Ω)
  targetSymmetric : @SymmetricCategory (DerivedCategory.PointFdQbar l Ω) _ targetMonoidal

attribute [instance_reducible, instance] CommonStructures.sourceMonoidal
attribute [instance_reducible, instance] CommonStructures.sourceSymmetric
attribute [instance_reducible, instance] CommonStructures.targetMonoidal
attribute [instance_reducible, instance] CommonStructures.targetSymmetric

/-- Every representative is mapped by the stated conjugation; the tensor component is
its common-field class with the specified phi-inverse then F(d) source transport.
Source: blueprint orders 1826, 1868, DAG proof steps 6--11
(blueprint: def-sf-common-tensor-comparison-descent). -/
structure CommonData [CommonStructures R] where
  stageTensor : ∀ E, (R.S.ι E).CoreMonoidal
  sourceAt : ∀ (P Q : R.S.PairCategory) (K : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K),
    (R.S.ι K).obj (tensorAt R P Q K a b) ≅ P ⊗ Q
  unitAt : ∀ E, (R.S.ι E).obj (𝟙_ (Rat C E)) ≅ 𝟙_ R.S.PairCategory
  G : R.S.PairCategory ⥤ DerivedCategory.PointFdQbar l Ω
  object : ∀ P, G.obj P = image R P
  stageComparison : ∀ E, R.S.ι E ⋙ G ≅ fdFunctor R E ⋙
    DerivedCategory.pointFdQbarStage l Ω E
  tensor : G.CoreMonoidal
  finiteTensor : ∀ (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L),
    DerivedCategory.pointFiniteDimensional (FieldOf l Ω L) (targetAt R P Q L a b)
  targetAtIso : ∀ (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L),
    (DerivedCategory.pointFdQbarStage l Ω L).obj
      ⟨targetAt R P Q L a b, finiteTensor P Q L a b⟩ ≅ G.obj P ⊗ G.obj Q
  omegaComparison : ∀ E : Index l Ω,
    DerivedCategory.PerfectScalar.B
        (omegaMap l Ω E) ≅
      DerivedCategory.fieldDerivedScalarExtension (omegaMap l Ω E).hom
  realization : (DerivedCategory.pointFdQbarRealization l Ω).CoreMonoidal
  finiteUnit : ∀ E : Index l Ω,
    DerivedCategory.pointFiniteDimensional (FieldOf l Ω E) (𝟙_ (D (FieldOf l Ω E)))
  targetUnit : ∀ E : Index l Ω,
    (DerivedCategory.pointFdQbarStage l Ω E).obj
      ⟨𝟙_ (D (FieldOf l Ω E)), finiteUnit E⟩ ≅
        𝟙_ (DerivedCategory.PointFdQbar l Ω)

/-- Common descent condition 1. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition1 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ E (X Y : Rat C E),
    (R.S.ι E).map (β_ X Y).hom ≫ ((datum.stageTensor E).μIso Y X).inv =
      ((datum.stageTensor E).μIso X Y).inv ≫ (β_ ((R.S.ι E).obj X) ((R.S.ι E).obj Y)).hom)

/-- Common descent condition 2. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition2 [CommonStructures R] (_datum : CommonData R) : Prop :=
  (∀ P Q : R.S.PairCategory,
    (P ⊗ Q).stage = Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)

/-- Common descent condition 3. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition3 [CommonStructures R] (_datum : CommonData R) : Prop :=
  (∀ P Q : R.S.PairCategory, HEq (P ⊗ Q).obj
    (tensorAt R P Q (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2))

/-- Common descent condition 4. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition4 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (K : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K),
    datum.sourceAt P Q K a b =
      ((datum.stageTensor K).μIso (P.toStage a) (Q.toStage b)).symm ≪≫
        tensorIso ((R.S.transIso a).app P.obj) ((R.S.transIso b).app Q.obj))

/-- Common descent condition 5. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition5 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (K L : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) (s : K ≤ L),
    (R.S.ι L).map (tensorMove R P Q K L a b s).hom ≫ (datum.sourceAt P Q L
        (a.trans s) (b.trans s)).hom =
      (R.S.transIso s).hom.app (tensorAt R P Q K a b) ≫ (datum.sourceAt P Q K a b).hom)

/-- Common descent condition 6. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition6 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (K L : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) (s : K ≤ L)
    (t : Padic.finiteCoefficientCompositum l Ω P.stage Q.stage ≤ L),
    HEq (datum.sourceAt P Q K a b).hom
      (StageSystem.PairCategory.mkHom
        (X := (R.S.ι K).obj (tensorAt R P Q K a b))
        (Y := ⟨Padic.finiteCoefficientCompositum l Ω P.stage Q.stage,
          tensorAt R P Q (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2⟩)
        L s t ((tensorMove R P Q K L a b s).hom ≫
          (tensorMove R P Q (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage) L
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 t).inv)))

/-- Common descent condition 7. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition7 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P P' Q Q' : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (a' : P'.stage ≤ L) (b : Q.stage ≤ L) (b' : Q'.stage ≤ L)
    (f : P.toStage a ⟶ P'.toStage a') (g : Q.toStage b ⟶ Q'.toStage b'),
    (datum.sourceAt P Q L a b).inv ≫ (R.S.ι L).map (f ⊗ₘ g) ≫
        (datum.sourceAt P' Q' L a' b').hom =
      (StageSystem.PairCategory.mkHom L a a' f) ⊗ₘ
        (StageSystem.PairCategory.mkHom L b b' g))

/-- Common descent condition 8. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition8 [CommonStructures R] (_datum : CommonData R) : Prop :=
  (𝟙_ R.S.PairCategory =
    ⟨Padic.finiteCoefficientBase l Ω, 𝟙_ (Rat C (Padic.finiteCoefficientBase l Ω))⟩)

/-- Common descent condition 9. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition9 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ E, datum.unitAt E = (datum.stageTensor E).εIso.symm)

/-- Common descent condition 10. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition10 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (E L : Index l Ω) (a : E ≤ L)
    (b : Padic.finiteCoefficientBase l Ω ≤ L),
    HEq (datum.unitAt E).hom
      (StageSystem.PairCategory.mkHom
        (X := (R.S.ι E).obj (𝟙_ (Rat C E)))
        (Y := ⟨Padic.finiteCoefficientBase l Ω,
          𝟙_ (Rat C (Padic.finiteCoefficientBase l Ω))⟩) L a b
        ((R.transitionTensor a).εIso.inv ≫ (R.transitionTensor b).εIso.hom)))

/-- Common descent condition 11. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition11 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ {E L} (a : E ≤ L),
    (R.S.ι L).map (R.transitionTensor a).εIso.inv ≫ (datum.unitAt L).hom =
      (R.S.transIso a).hom.app (𝟙_ (Rat C E)) ≫ (datum.unitAt E).hom)

/-- Common descent condition 12. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition12 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L) (f : P.toStage a ⟶ Q.toStage b),
    HEq (datum.G.map (StageSystem.PairCategory.mkHom L a b f))
      ((imageStage R P L a).inv ≫
        (DerivedCategory.pointFdQbarStage l Ω L).map
          (ObjectProperty.homMk
            (X := (DerivedCategory.pointFdScalarExtension (fieldMap l Ω a).hom).obj
              ((fdFunctor R P.stage).obj P.obj))
            (Y := (DerivedCategory.pointFdScalarExtension (fieldMap l Ω b).hom).obj
              ((fdFunctor R Q.stage).obj Q.obj))
            ((R.phi a).inv.app P.obj ≫ (R.F L).map f ≫
            (R.phi b).hom.app Q.obj)) ≫ (imageStage R Q L b).hom))

/-- Common descent condition 13. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition13 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ E (X : Rat C E),
    (datum.stageComparison E).hom.app X = eqToHom (datum.object ((R.S.ι E).obj X)))

/-- Common descent condition 14. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition14 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ P Q : R.S.PairCategory,
    datum.G.map (β_ P Q).hom ≫ (datum.tensor.μIso Q P).inv =
      (datum.tensor.μIso P Q).inv ≫ (β_ (datum.G.obj P) (datum.G.obj Q)).hom)

/-- Common descent condition 15. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition15 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (E : Index l Ω) (P : CochainComplex (ModuleCat.{u} (FieldOf l Ω E)) ℤ),
    (datum.omegaComparison E).hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.extendScalars (omegaMap l Ω E).hom).mapDerivedCategoryFactors.hom.app P =
      DerivedCategory.PerfectScalar.modelMap.{u, u} (omegaMap l Ω E) P)

/-- Common descent condition 16. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition16 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L),
    HEq ((DerivedCategory.pointFdQbarRealization l Ω).map
        (datum.targetAtIso P Q L a b).hom ≫
          (datum.realization.μIso (datum.G.obj P) (datum.G.obj Q)).inv)
      ((datum.omegaComparison L).inv.app (targetAt R P Q L a b) ≫
        (scalarTensor (omegaMap l Ω L) _ _
          (R.extendedPerfect a P.obj) (R.extendedPerfect b Q.obj)).hom ≫
        ((datum.omegaComparison L).hom.app _ ⊗ₘ (datum.omegaComparison L).hom.app _) ≫
        ((DerivedCategory.fieldScalarTower (fieldMap l Ω a).hom (omegaMap l Ω L).hom).hom.app
            ((R.F P.stage).obj P.obj) ⊗ₘ
          (DerivedCategory.fieldScalarTower (fieldMap l Ω b).hom (omegaMap l Ω L).hom).hom.app
            ((R.F Q.stage).obj Q.obj))))

/-- Common descent condition 17. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition17 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ P Q : DerivedCategory.PointFdQbar l Ω,
    (DerivedCategory.pointFdQbarRealization l Ω).map (β_ P Q).hom ≫
        (datum.realization.μIso Q P).inv =
      (datum.realization.μIso P Q).inv ≫
        (DerivedCategory.PerfectScalar.symmetry.{u, u} (CommRingCat.of Ω)
          ((DerivedCategory.pointFdQbarRealization l Ω).obj P)
          ((DerivedCategory.pointFdQbarRealization l Ω).obj Q)).hom)

/-- Common descent condition 18. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition18 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ E : Index l Ω,
    (DerivedCategory.pointFdQbarRealization l Ω).map (datum.targetUnit E).hom ≫
        datum.realization.εIso.inv =
      (datum.omegaComparison E).inv.app (𝟙_ (D (FieldOf l Ω E))) ≫
        (scalarUnit (omegaMap l Ω E)).hom)

/-- Common descent condition 19. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition19 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L),
    datum.G.map (datum.sourceAt P Q L a b).hom ≫ (datum.tensor.μIso P Q).inv =
      (datum.stageComparison L).hom.app (tensorAt R P Q L a b) ≫
        (DerivedCategory.pointFdQbarStage l Ω L).map
          (ObjectProperty.homMk
            (X := (fdFunctor R L).obj (tensorAt R P Q L a b))
            (Y := ⟨targetAt R P Q L a b, datum.finiteTensor P Q L a b⟩)
            (gamma R P Q L a b).hom) ≫ (datum.targetAtIso P Q L a b).hom)

/-- Common descent condition 20. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition20 [CommonStructures R] (_datum : CommonData R) : Prop :=
  (∀ (P Q : R.S.PairCategory) (K L : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) (s : K ≤ L),
    (R.phi s).inv.app (tensorAt R P Q K a b) ≫
        (R.F L).map (tensorMove R P Q K L a b s).hom ≫
        (gamma R P Q L (a.trans s) (b.trans s)).hom =
      (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω s).hom).map
        (gamma R P Q K a b).hom ≫ targetMove R P Q K L a b s)

/-- Common descent condition 21. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
def CommonData.condition21 [CommonStructures R] (datum : CommonData R) : Prop :=
  (∀ E,
    datum.G.map (datum.unitAt E).hom ≫ datum.tensor.εIso.inv =
      (datum.stageComparison E).hom.app (𝟙_ (Rat C E)) ≫
        (DerivedCategory.pointFdQbarStage l Ω E).map
          (ObjectProperty.homMk
            (X := (fdFunctor R E).obj (𝟙_ (Rat C E)))
            (Y := ⟨𝟙_ (D (FieldOf l Ω E)), datum.finiteUnit E⟩)
            (R.tensor E).εIso.inv) ≫ (datum.targetUnit E).hom)

/-- All common-stage formulas. Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-descent). -/
structure CommonData.Valid [CommonStructures R] (datum : CommonData R) : Prop where
  stageSymmetric : datum.condition1
  tensorStage : datum.condition2
  tensorObject : datum.condition3
  sourceAtFormula : datum.condition4
  sourceAtTransport : datum.condition5
  sourceAtClass : datum.condition6
  tensorArrow : datum.condition7
  unitObject : datum.condition8
  unitAtFormula : datum.condition9
  unitAtClass : datum.condition10
  unitAtTransport : datum.condition11
  arrow : datum.condition12
  stageComparisonFormula : datum.condition13
  symmetric : datum.condition14
  omegaModel : datum.condition15
  targetAtFormula : datum.condition16
  realizationSymmetric : datum.condition17
  targetUnitFormula : datum.condition18
  tensorFormula : datum.condition19
  transportEquation : datum.condition20
  unitFormula : datum.condition21
end WeilConjectures.TensorComparisonDescent
