/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkUnit
public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.RationalConstantUnitFrobenius
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import WeilConjectures.SmoothPurity.Common.CommonStageCompositorIntegralNormalization

/-! # Frobenius coherence of the normalized constant unit

Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Scheme.residueField completedIntegralCoefficientSheafUnrestricted

section Unit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant-section unit into completed pullback is determined by its finite
unit generators and zero shifted-cone component, for an arbitrary scheme morphism.
Source: constant comparison in the six-step proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: finite extension of scalars takes the regular module to the regular module.
Apply its adjunction unit to 1 tensor 1 at every quotient. These elements commute
with the actual quotient maps; their product is killed by 1-shift. The mapping
cocone lift with second component zero gives the displayed map. A module map out
of the regular sheaf is determined by the image of 1 on the terminal site object;
restriction determines the image on every other object. The two cone projections
then give uniqueness in every degree. This also covers the empty scheme. -/
theorem chainUnit_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E f).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0) := by
  exact ConstantGeometricStalkUnit.integralChainUnit_existsUnique l E f

/-- The uniquely specified whole-tower unit, with its fixed zero cone coordinate.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def chainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (chainUnit_existsUnique l E f).exists.choose

/-- The strict unit is a quasi-isomorphism before rationalization.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: finite unit multiplication identifies the whole pullback tower with the
quotient coefficient tower of X, including its actual quotient transitions.
Those transitions are surjective. The Roos complex therefore has only degree-zero
cohomology, equal to the completed coefficient sheaf. The normalized chain unit
induces this identity and is consequently a quasi-isomorphism. -/
theorem chainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (DerivedCategory.Q.map (chainUnit l E f)) := by
  simpa only [chainUnit, ConstantGeometricStalkUnit.integralChainUnit] using
    ConstantGeometricStalkUnit.integralChainUnit_isIso l E f

/-- The usual completed pullback-of-unit identification, using the actual good
representative comparison followed by the inverse normalized whole-tower unit.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def integralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E f).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (chainUnit l E f))
      (chainUnit_isIso l E f)).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Rationalize that particular unit map, retaining the prescribed object comparison.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def rationalUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (rationalDerivedPullback l E f).obj (constantWeilRationalObject l E D hl Y) ≅
      constantWeilRationalObject l E D hl X :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralUnit l E f))
end Unit

section CommonUnit
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The coefficient unit as its literal least-stage object, without a Weil structure.
Source: canonical constant-pair convention, clause 5
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def unit (T : Scheme.{u}) : generalAlgebraicallyClosedConstructibleCategory l Ω T :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)).obj
    (constantWeilRationalObject l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
      D hl T)

/-- Common-stage unit comparison: represent the rationalized strict unit at Q_l.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def commonUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (commonStageDerivedPullback l Ω f).obj (unit D l hl Ω Y) ≅ unit D l hl Ω X :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)).mapIso
      (rationalUnit l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
        D hl f)
end CommonUnit

private theorem unit_conjugation {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) (S : C ⥤ C) (T : B ⥤ B)
    (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 B) {P Q : C} (a : P ⟶ Q)
    (bP : T.obj (F.obj P) ≅ F.obj (S.obj P))
    (bQ : T.obj (F.obj Q) ≅ F.obj (S.obj Q))
    (hP : bP ≪≫ F.mapIso (s.app P) = t.app (F.obj P))
    (hQ : bQ ≪≫ F.mapIso (s.app Q) = t.app (F.obj Q)) :
    bP.hom ≫ F.map (S.map a) ≫ bQ.inv = T.map (F.map a) := by
  apply (cancel_mono bQ.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (F.map (s.hom.app Q))).1
  have hp := congrArg Iso.hom hP
  have hq := congrArg Iso.hom hQ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hp hq
  rw [Category.assoc, ← F.map_comp, s.hom.naturality, F.map_comp,
    ← Category.assoc, hp, Category.assoc, hq]
  exact (t.hom.naturality (F.map a)).symm

-- Normalize cached category wrappers without unfolding the derived constructions.
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  commonStagePullbackComparison
  sfRationalScalarExtension operationStageTransitionIso
  GeneralAlgebraicallyClosedCoefficients.unitor
  StageSystem.PairCategory.mkHom ScalarLocalization.category
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  StageSystem.PairCategory.categoryStruct Preadditive.fullSubcategory
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.ι commonStagePullbackObject
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

/-- Finite-stage representative formula for the common-stage pullback.
Source: the common-stage passage in the normalized constant-unit proof.
(blueprint: lem-pur-common-constant-unit-frobenius-transport).
Proof: apply the prescribed map formula to the self-stage representative of a.
The coefficient-unit normalization identifies each boundary comparison after
composition with the transition unitor. Naturality of that unitor cancels the
boundary comparisons, leaving the self-transition of the rational pullback map.
Its representative is exactly the stage inclusion. The recorded object
comparisons account for the heterogeneous endpoints. -/
theorem commonStageDerivedPullback_map_inclusion
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (P Q : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L)
    (a : P ⟶ Q) :
    HEq
      ((commonStageDerivedPullback l Ω f).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map a))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map a)) := by
  unfold commonStageDerivedPullback
  have hm := (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
    ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P)
    ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj Q) L le_rfl le_rfl
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T (le_refl L)).map a)
  have hc := unit_conjugation
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T (le_refl L))
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T (le_refl L))
    (operationStageTransitionIso l Ω Y L L le_rfl ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y L)
    (operationStageTransitionIso l Ω X L L le_rfl ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor l Ω X L)
    a
    (commonStagePullbackComparison l Ω f
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P) L le_rfl)
    (commonStagePullbackComparison l Ω f
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj Q) L le_rfl)
    (commonStagePullbackComparison_self_unit l Ω f _)
    (commonStagePullbackComparison_self_unit l Ω f _)
  exact hm.trans (heq_of_eq (congrArg
    (GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Ω f
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P))
      (commonStagePullbackObject l Ω f
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj Q)) L le_rfl le_rfl) hc))

private theorem map_heq {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {A B A' B' : C} (ha : A = A') (hb : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases ha
  cases hb
  cases h
  rfl

private theorem inv_heq {C : Type*} [Category* C]
    {A B A' B' : C} (ha : A = A') (hb : B = B')
    {a : A ≅ B} {b : A' ≅ B'} (h : HEq a.hom b.hom) : HEq a.inv b.inv := by
  cases ha
  cases hb
  have e : a = b := Iso.ext (eq_of_heq h)
  cases e
  rfl

private theorem comp_heq {C : Type*} [Category* C]
    {A B D A' B' D' : C}
    {a : A ⟶ B} {b : B ⟶ D} {a' : A' ⟶ B'} {b' : B' ⟶ D'}
    (ha : HEq a a') (hb : HEq b b') (hA : A = A') (hB : B = B') (hD : D = D') :
    HEq (a ≫ b) (a' ≫ b') :=
  heq_comp hA hB hD ha hb

private theorem map_three_two {C B : Type*} [Category* C] [Category* B] (I : C ⥤ B)
    {A₀ A₁ A₂ A₃ A₄ : C} {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃}
    {d : A₀ ⟶ A₄} {e : A₄ ⟶ A₃} (h : a ≫ b ≫ c = d ≫ e) :
    I.map a ≫ I.map b ≫ I.map c = I.map d ≫ I.map e := by
  simpa only [Functor.map_comp] using congrArg I.map h

private theorem eqToHom_map_heq {C B : Type*} [Category* C] [Category* B]
    (I : C ⥤ B) {α : Sort*} (F : α → B) (G : α → C)
    (ho : ∀ a, F a = I.obj (G a)) {a b : α} (h : a = b) :
    HEq (eqToHom (congrArg F h)) (I.map (eqToHom (congrArg G h))) := by
  cases h
  change HEq (𝟙 (F a)) (I.map (𝟙 (G a)))
  rw [I.map_id]
  have hid {U V : B} (e : U = V) : HEq (𝟙 U) (𝟙 V) := by
    cases e
    rfl
  exact hid (ho a)

private theorem pullback_stage_obj
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj P) := by
  unfold commonStageDerivedPullback
  exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _

private theorem pullback_stage_obj_two
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) :
    (commonStageDerivedPullback l Ω g).obj
        ((commonStageDerivedPullback l Ω f).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P)) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
          ((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj P)) := by
  exact (congrArg (commonStageDerivedPullback l Ω g).obj
    (pullback_stage_obj l Ω f L P)).trans (pullback_stage_obj l Ω g L _)

private theorem square_stage_heq
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) :
    HEq (podCommonSquarePullbackComponent l Ω f gX gY h
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P)).hom
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        (podRationalSquarePullbackComponent l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f gX gY h P).hom) := by
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L
  have ho (k : X ⟶ Y) := pullback_stage_obj l Ω k L P
  have hleft : HEq
      (pullbackTensorCommonComposition l Ω f gX
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P)).hom
      (I.map (pullbackTensorRationalComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f gX P).hom) :=
    commonStageCompositor_integral l Ω gX f _
  have hright : HEq
      (pullbackTensorCommonComposition l Ω gY f
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P)).hom
      (I.map (pullbackTensorRationalComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) gY f P).hom) :=
    commonStageCompositor_integral l Ω f gY _
  have hi := inv_heq
    (a := pullbackTensorCommonComposition l Ω f gX
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P))
    (b := I.mapIso (pullbackTensorRationalComposition l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f gX P))
    (ho (gX ≫ f)) (pullback_stage_obj_two l Ω f gX L P) hleft
  have hm := eqToHom_map_heq I
    (fun k : X ⟶ Y ↦ (commonStageDerivedPullback l Ω k).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj P))
    (fun k : X ⟶ Y ↦ (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k).obj P) ho h
  have hc := comp_heq hm hright (ho (gX ≫ f)) (ho (f ≫ gY))
    (pullback_stage_obj_two l Ω gY f L P)
  have hall := comp_heq hi hc (pullback_stage_obj_two l Ω f gX L P)
    (ho (gX ≫ f)) (pullback_stage_obj_two l Ω gY f L P)
  simp only [Functor.mapIso_inv] at hall
  rw [← I.map_comp, ← I.map_comp] at hall
  simpa only [podCommonSquarePullbackComponent, podRationalSquarePullbackComponent,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom] using hall

set_option allowUnsafeReducibility true in
attribute [local reducible] FiniteFieldDatum.geometricFiber CategoryTheory.Aut

/-- The normalized completed constant unit commutes with the geometric Frobenius square.
Source: purity/trace equivariance proof, canonical constant comparison preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius).
Proof: apply rationalizedUnit_frobenius at the least coefficient field. Its unit
agrees with rationalUnit because both use the same uniquely normalized strict chain
unit. The common unit and constant Weil structures are the included rational maps,
preceded by their recorded object comparisons. The inclusion map formula identifies
both pullbacks of these arrows. The common compositor normalization identifies the
square comparison, including its inverse and the equality of scheme composites.
Functoriality of the inclusion and heterogeneous composition therefore transport the
rational equation to the displayed equation. This also covers empty schemes and
identity morphisms. -/
theorem commonUnit_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    let f := FrobeniusExchange.fiberMap D f₀
    let K := unit D l hl Ω (D.geometricFiber Y₀).left
    let u := commonUnit D l hl Ω f
    (podCommonSquarePullbackComponent l Ω f
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (commonStageDerivedPullback l Ω f).map
          (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str.hom ≫ u.hom =
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map u.hom ≫
        (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str.hom  := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let L := Padic.finiteCoefficientBase l Ω
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  let f := FrobeniusExchange.fiberMap D f₀
  let X := (D.geometricFiber X₀).left
  let Y := (D.geometricFiber Y₀).left
  let gX := (D.geometricFrobenius X₀).hom
  let gY := (D.geometricFrobenius Y₀).hom
  let IX := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L
  let IY := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) L
  let KY := constantWeilRationalObject l E D hl Y
  let KX := constantWeilRationalObject l E D hl X
  let u := rationalizedUnit D l hl E f
  have hu : HEq (commonUnit D l hl Ω f).hom (IX.map u.hom) := by
    change HEq (eqToHom (pullback_stage_obj l Ω f L KY) ≫
      IX.map (rationalUnit l E D hl f).hom) _
    exact (eqToHom_comp_heq _ _).trans (by rfl)
  have htY : HEq (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str.hom
      (IY.map (constantWeilRationalComplex l E D hl Y₀).str.hom) := by
    change HEq (eqToHom (pullback_stage_obj l Ω gY L KY) ≫
      IY.map (constantWeilRationalComplex l E D hl Y₀).str.hom) _
    exact eqToHom_comp_heq _ _
  have htX : HEq (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str.hom
      (IX.map (constantWeilRationalComplex l E D hl X₀).str.hom) := by
    change HEq (eqToHom (pullback_stage_obj l Ω gX L KX) ≫
      IX.map (constantWeilRationalComplex l E D hl X₀).str.hom) _
    exact eqToHom_comp_heq _ _
  have hfu := (map_heq (commonStageDerivedPullback l Ω gX)
      (pullback_stage_obj l Ω f L KY) rfl hu).trans
    (commonStageDerivedPullback_map_inclusion l Ω gX L _ _ u.hom)
  have hft := (map_heq (commonStageDerivedPullback l Ω f)
      (pullback_stage_obj l Ω gY L KY) rfl htY).trans
    (commonStageDerivedPullback_map_inclusion l Ω f L _ _
      (constantWeilRationalComplex l E D hl Y₀).str.hom)
  have hs := square_stage_heq l Ω f gX gY (zlFrobenius_naturality D f₀) L KY
  have hleft := comp_heq hs
    (comp_heq hft hu (pullback_stage_obj_two l Ω gY f L KY)
      (pullback_stage_obj l Ω f L KY) rfl)
    (pullback_stage_obj_two l Ω f gX L KY)
    (pullback_stage_obj_two l Ω gY f L KY) rfl
  have hright := comp_heq hfu htX (pullback_stage_obj_two l Ω f gX L KY)
    (pullback_stage_obj l Ω gX L KX) rfl
  have he := map_three_two IX (rationalizedUnit_frobenius D l hl E X₀ Y₀ f₀)
  exact eq_of_heq (hleft.trans ((heq_of_eq he).trans hright.symm))

end WeilConjectures.ConstantPurityFrobenius
