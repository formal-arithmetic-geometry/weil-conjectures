/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.DirectImagesConstructible
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.PathCategory.Basic
import Sheaf.Paper.RestrictionTensorRepresentativeTransport

/-! # Descent of restriction tensor and unit comparisons

Source: main-20261015, def-pur-section-invariant, final invertibility assertion;
the agent-written common-stage subargument in the DAG
(blueprint: lem-pur-common-stage-restriction-tensor-descent).

The named expressions below use the published operations and their canonical comparisons.
Residue-field inverses come from the fixed base field, without extra hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

set_option allowUnsafeReducibility true in
attribute [local reducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
  WeilConjectures.commonStagePullbackObject WeilConjectures.commonStageTensorObject

namespace WeilConjectures.CommonStageRestrictionTensor

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor
  rationalPullbackScalarComparison rationalTensorScalarComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem mapHEq {C : Type*} [Category* C] {C' : Type*} [Category* C']
    (F : C ⥤ C') {A B A' B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {a' : A' ⟶ B'} (ha : HEq a a') : HEq (F.map a) (F.map a') := by
  cases hA
  cases hB
  cases ha
  rfl

private theorem prodHomHEq {C : Type*} [Category* C]
    {A B C₀ D₀ A' B' C' D' : C} (hA : A = A') (hB : B = B')
    (hC : C₀ = C') (hD : D₀ = D') {a : A ⟶ B} {b : C₀ ⟶ D₀}
    {a' : A' ⟶ B'} {b' : C' ⟶ D'} (ha : HEq a a') (hb : HEq b b') :
    HEq (Prod.mkHom a b) (Prod.mkHom a' b') := by
  cases hA
  cases hB
  cases hC
  cases hD
  cases ha
  cases hb
  rfl

private def representativeIso {J : Type*} [Preorder J] [IsDirectedOrder J]
    {C : J → Type*} [∀ j, Category (C j)] (S : StageSystem C)
    (X Y : S.PairCategory) (j : J) (hX : X.stage ≤ j) (hY : Y.stage ≤ j)
    (c : X.toStage hX ≅ Y.toStage hY) : X ≅ Y :=
  S.isoToStage X hX ≪≫ (S.ι j).mapIso c ≪≫ (S.isoToStage Y hY).symm

private theorem representativeIso_hom {J : Type*} [Preorder J] [IsDirectedOrder J]
    {C : J → Type*} [∀ j, Category (C j)] (S : StageSystem C)
    (X Y : S.PairCategory) (j : J) (hX : X.stage ≤ j) (hY : Y.stage ≤ j)
    (c : X.toStage hX ≅ Y.toStage hY) :
    (representativeIso S X Y j hX hY c).hom =
      StageSystem.PairCategory.mkHom j hX hY c.hom := by
  dsimp only [representativeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact (StageSystem.mkHom_eq_isoToStage hX hY c.hom).symm

private theorem isoConjHEq {C : Type*} [Category* C] {A B X Y : C}
    (hA : A = X) (hB : B = Y) (e : X ≅ Y) :
    HEq (eqToIso hA ≪≫ e ≪≫ (eqToIso hB).symm).hom e.hom := by
  exact (conj_eqToHom_iff_heq _ _ hA hB).1 rfl

private theorem tensorConjugation {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B A' B' X Y X' Y' : C}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') :
    T.map (Prod.mkHom (a.hom ≫ f ≫ a'.inv) (b.hom ≫ g ≫ b'.inv)) =
      (T.mapIso (Iso.prod a b)).hom ≫ T.map (Prod.mkHom f g) ≫
        (T.mapIso (Iso.prod a' b')).inv := by
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← T.map_comp, ← T.map_comp]
  rfl

private theorem mappedCoordinate {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) {A B X Y : C} {P Q : D}
    (a : A ≅ X) (b : B ≅ Y) (p : P ≅ R.obj A) (q : Q ≅ R.obj B)
    (f : X ⟶ Y) :
    p.hom ≫ R.map (a.hom ≫ f ≫ b.inv) ≫ q.inv =
      (p ≪≫ R.mapIso a).hom ≫ R.map f ≫ (q ≪≫ R.mapIso b).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]

private theorem tensorCoordinate {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B A' B' X Y X' Y' : C} {P Q : D}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (p : P ≅ T.obj (A, B)) (q : Q ≅ T.obj (A', B'))
    (f : X ⟶ X') (g : Y ⟶ Y') :
    p.hom ≫ T.map (Prod.mkHom (a.hom ≫ f ≫ a'.inv) (b.hom ≫ g ≫ b'.inv)) ≫ q.inv =
      (p ≪≫ T.mapIso (Iso.prod a b)).hom ≫ T.map (Prod.mkHom f g) ≫
        (q ≪≫ T.mapIso (Iso.prod a' b')).inv := by
  rw [tensorConjugation]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

private theorem conjugateNaturality {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (mu : F ≅ G) {a b : C} (f : a ⟶ b)
    {X X' Y Y' : D} (p : X ≅ F.obj a) (p' : X' ≅ F.obj b)
    (q : Y ≅ G.obj a) (q' : Y' ≅ G.obj b) :
    (p.hom ≫ F.map f ≫ p'.inv) ≫ (p' ≪≫ mu.app b ≪≫ q'.symm).hom =
      (p ≪≫ mu.app a ≪≫ q.symm).hom ≫ (q.hom ≫ G.map f ≫ q'.inv) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ p.hom ≫ k ≫ q'.inv) (mu.hom.naturality f)

private theorem unitCoordinate
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (S : C₀ ⥤ C₁) (T : D₀ ⥤ D₁)
    (S' : C₀ ⥤ C₁) (T' : D₀ ⥤ D₁) (x : S' ≅ S) (y : T' ≅ T)
    (b : R₀ ⋙ T ≅ S ⋙ R₁) (U : C₀) (V : D₀) (W : C₁) (Z : D₁)
    (e₀ : R₀.obj U ≅ V) (e₁ : R₁.obj W ≅ Z)
    (u : S.obj U ≅ W) (v : T.obj V ≅ Z)
    (hmix : T.map e₀.hom ≫ v.hom = b.hom.app U ≫ R₁.map u.hom ≫ e₁.hom) :
    ((y.app (R₀.obj U) ≪≫ b.app U ≪≫ R₁.mapIso (x.app U).symm) ≪≫
      R₁.mapIso (x.app U ≪≫ u)).hom ≫ e₁.hom ≫ (y.app V ≪≫ v).inv =
        T'.map e₀.hom := by
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R₁.map_comp_assoc]
  simp only [Iso.inv_hom_id_app, R₁.map_id, Category.id_comp]
  rw [← reassoc_of% hmix]
  simp only [Iso.hom_inv_id_assoc]
  rw [← y.hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

/-- The coefficient prime is invertible in each residue field by base-field transport.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[instance_reducible] def residueUnits (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    ∀ w : W, Invertible (l : W.residueField w) :=
  fun w ↦ (Eq.mp (congrArg IsUnit (map_natCast
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop ≫
      W.Γevaluation w).hom l))
        ((finiteFieldDatumPrimeUnit D l hl).map
          ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop ≫
            W.Γevaluation w).hom)).invertible

attribute [local irreducible] residueUnits

/-- The recorded rational restriction functor at E.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def r {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) :
    Stage l Ω X E ⥤ Stage l Ω Y E :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  rationalDerivedPullback l (Coefficient.{u} l Ω E) f

/-- The recorded rational tensor functor at E.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def t (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    Stage l Ω W E × Stage l Ω W E ⥤ Stage l Ω W E :=
  letI := residueUnits D l hl W
  rationalDerivedTensor l (Coefficient.{u} l Ω E) W

/-- Restriction on the raw common-stage category.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def rOmega {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) : Pair l Ω X ⥤ Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageDerivedPullback l Ω f

/-- Tensor on the raw common-stage category.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def tOmega (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    Pair l Ω W × Pair l Ω W ⥤ Pair l Ω W :=
  letI := residueUnits D l hl W
  commonStageDerivedTensor l Ω W

private theorem rOmega_obj {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A : Pair l Ω X) :
    (rOmega D l hl Ω f).obj A =
      (letI := residueUnits D l hl X
       letI := residueUnits D l hl Y
       commonStagePullbackObject l Ω f A) := by
  let _ := residueUnits D l hl X
  let _ := residueUnits D l hl Y
  unfold rOmega commonStageDerivedPullback
  exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A

private theorem tOmega_obj (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    (A B : Pair l Ω W) :
    (tOmega D l hl Ω W).obj (A, B) =
      (letI := residueUnits D l hl W
       commonStageTensorObject l Ω W A B) := by
  let _ := residueUnits D l hl W
  unfold tOmega commonStageDerivedTensor
  exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 A B

/-- The specified rationalized scalar restriction comparison, not arbitrary data.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def b {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E L : Index l Ω) (h : E ≤ L) :
    r D l hl Ω f E ⋙ transition l Ω Y E L h ≅
      transition l Ω X E L h ⋙ r D l hl Ω f L :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  show rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙
      sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) ≅
    sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) ⋙ rationalDerivedPullback l (Coefficient.{u} l Ω L) f
  from rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f

/-- The specified rationalized scalar tensor comparison.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def theta (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E L : Index l Ω) (h : E ≤ L) :=
  letI := residueUnits D l hl W
  rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W

/-- The rationalized completed coefficient unit.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    Stage l Ω W E :=
  constantWeilRationalObject l (Coefficient.{u} l Ω E) D hl W

/-- The normalized coefficient-unit scalar identification.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def upsilon (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω W E L h).obj (unit D l hl Ω W E) ≅ unit D l hl Ω W L :=
  constantCoefficientRationalScalarIso l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W D hl

/-- The literal source pair of the tensor comparison.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def source {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackObject l Ω f (commonStageTensorObject l Ω X A B)

/-- The literal target pair of the tensor comparison.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def target {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorObject l Ω Y
    (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)

/-- The canonical source endpoint identification at a common field.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def sourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (source D l hl Ω f A B).stage ≤ L) :
    (source D l hl Ω f A B).toStage h ≅
      (r D l hl Ω f L).obj ((t D l hl Ω X L).obj
        (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          A.stage B.stage).1.trans h),
         B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          A.stage B.stage).2.trans h))) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h ≪≫
    (r D l hl Ω f L).mapIso (commonStageTensorComparison l Ω X A B L h)

/-- The target identification includes tensor and restriction conjugations.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def targetComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (target D l hl Ω f A B).stage ≤ L) :
    (target D l hl Ω f A B).toStage h ≅
      (t D l hl Ω Y L).obj
        ((r D l hl Ω f L).obj (A.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h)),
         (r D l hl Ω f L).obj (B.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h))) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorComparison l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h ≪≫
    (t D l hl Ω Y L).mapIso (Iso.prod
      (commonStagePullbackComparison l Ω f A L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h))
      (commonStagePullbackComparison l Ω f B L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)))


private theorem source_obj {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) :
    ((tOmega D l hl Ω X) ⋙ rOmega D l hl Ω f).obj (A, B) =
      source D l hl Ω f A B := by
  change (rOmega D l hl Ω f).obj ((tOmega D l hl Ω X).obj (A, B)) = _
  rw [tOmega_obj, rOmega_obj]

private theorem target_obj {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) :
    ((rOmega D l hl Ω f).prod (rOmega D l hl Ω f) ⋙ tOmega D l hl Ω Y).obj
        (A, B) = target D l hl Ω f A B := by
  change (tOmega D l hl Ω Y).obj
    ((rOmega D l hl Ω f).obj A, (rOmega D l hl Ω f).obj B) = _
  rw [rOmega_obj, rOmega_obj, tOmega_obj]

attribute [local irreducible] rOmega tOmega

private theorem rOmega_map {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (a : A.toStage hA ⟶ B.toStage hB) :
    letI := residueUnits D l hl X
    letI := residueUnits D l hl Y
    HEq ((rOmega D l hl Ω f).map (ofHom A B L hA hB a))
      (ofHom (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)
        L hA hB ((commonStagePullbackComparison l Ω f A L hA).hom ≫
          (r D l hl Ω f L).map a ≫ (commonStagePullbackComparison l Ω f B L hB).inv)) := by
  let _ := residueUnits D l hl X
  let _ := residueUnits D l hl Y
  unfold rOmega commonStageDerivedPullback
  exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2 A B L hA hB a

private theorem tOmega_map (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    (A B A' B' : Pair l Ω W) (L : Index l Ω)
    (h : Padic.finiteCoefficientCompositum l Ω A.stage B.stage ≤ L)
    (h' : Padic.finiteCoefficientCompositum l Ω A'.stage B'.stage ≤ L)
    (a : A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).1.trans h) ⟶ A'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h'))
    (b : B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) ⟶ B'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h')) :
    letI := residueUnits D l hl W
    HEq ((tOmega D l hl Ω W).map (Prod.mkHom (ofHom A A' L
      (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h)
      (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h') a)
      (ofHom B B' L (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans
        h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h') b)))
      (ofHom (commonStageTensorObject l Ω W A B) (commonStageTensorObject l Ω W A' B')
        L h h' ((commonStageTensorComparison l Ω W A B L h).hom ≫
          (t D l hl Ω W L).map (Prod.mkHom a b) ≫
          (commonStageTensorComparison l Ω W A' B' L h').inv)) := by
  let _ := residueUnits D l hl W
  unfold tOmega commonStageDerivedTensor
  exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2
    A B A' B' L h h' a b

attribute [local irreducible] b theta commonStagePullbackComparison

private theorem source_map {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B A' B' : Pair l Ω X)
    (L : Index l Ω) (h : (source D l hl Ω f A B).stage ≤ L)
    (h' : (source D l hl Ω f A' B').stage ≤ L)
    (a : A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).1.trans h) ⟶ A'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h'))
    (b : B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) ⟶ B'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h')) :
    HEq ((tOmega D l hl Ω X ⋙ rOmega D l hl Ω f).map
      (Prod.mkHom (ofHom A A' L (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage
        B.stage).1.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).1.trans h') a) (ofHom B B' L (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).2.trans h') b)))
      (ofHom (source D l hl Ω f A B) (source D l hl Ω f A' B') L h h'
        ((sourceComparison D l hl Ω f A B L h).hom ≫
          (r D l hl Ω f L).map ((t D l hl Ω X L).map (Prod.mkHom a b)) ≫
          (sourceComparison D l hl Ω f A' B' L h').inv)) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let _ := residueUnits D l hl X
      let _ := residueUnits D l hl Y
      have ht := tOmega_map D l hl Ω X A B A' B' L h h' a b
      have hr := rOmega_map D l hl Ω f
        (commonStageTensorObject l Ω X A B) (commonStageTensorObject l Ω X A' B')
        L h h'
          ((commonStageTensorComparison l Ω X A B L h).hom ≫
            (t D l hl Ω X L).map (Prod.mkHom a b) ≫
              (commonStageTensorComparison l Ω X A' B' L h').inv)
      apply (mapHEq (rOmega D l hl Ω f)
        (tOmega_obj D l hl Ω X A B) (tOmega_obj D l hl Ω X A' B') ht).trans
      apply hr.trans
      apply heq_of_eq
      change ofHom (source D l hl Ω f A B) (source D l hl Ω f A' B') L h h' _ = _
      apply congrArg (ofHom (source D l hl Ω f A B)
        (source D l hl Ω f A' B') L h h')
      exact mappedCoordinate (r D l hl Ω f L)
        (commonStageTensorComparison l Ω X A B L h)
        (commonStageTensorComparison l Ω X A' B' L h')
        (commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h)
        (commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A' B') L h')
        ((t D l hl Ω X L).map (Prod.mkHom a b))


private theorem target_map {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B A' B' : Pair l Ω X)
    (L : Index l Ω) (h : (source D l hl Ω f A B).stage ≤ L)
    (h' : (source D l hl Ω f A' B').stage ≤ L)
    (a : A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).1.trans h) ⟶ A'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h'))
    (b : B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) ⟶ B'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h')) :
    HEq (((rOmega D l hl Ω f).prod (rOmega D l hl Ω f) ⋙ tOmega D l hl Ω Y).map
      (Prod.mkHom (ofHom A A' L (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage
        B.stage).1.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).1.trans h') a) (ofHom B B' L (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).2.trans h') b)))
      (ofHom (target D l hl Ω f A B) (target D l hl Ω f A' B') L h h'
        ((targetComparison D l hl Ω f A B L h).hom ≫
          (t D l hl Ω Y L).map (Prod.mkHom ((r D l hl Ω f L).map a)
            ((r D l hl Ω f L).map b)) ≫
          (targetComparison D l hl Ω f A' B' L h').inv)) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let _ := residueUnits D l hl X
      let _ := residueUnits D l hl Y
      have ha := rOmega_map D l hl Ω f A A' L (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).1.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).1.trans h') a
      have hb := rOmega_map D l hl Ω f B B' L (((Padic.finiteCoefficientFields_properties l Ω).1
        A.stage B.stage).2.trans h) (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage
        B'.stage).2.trans h') b
      have hp := prodHomHEq (rOmega_obj D l hl Ω f A) (rOmega_obj D l hl Ω f A')
        (rOmega_obj D l hl Ω f B) (rOmega_obj D l hl Ω f B') ha hb
      have ht := tOmega_map D l hl Ω Y (commonStagePullbackObject l Ω f A)
        (commonStagePullbackObject l Ω f B) (commonStagePullbackObject l Ω f A')
        (commonStagePullbackObject l Ω f B') L h h'
          ((commonStagePullbackComparison l Ω f A L _).hom ≫
            (r D l hl Ω f L).map a ≫ (commonStagePullbackComparison l Ω f A' L _).inv)
          ((commonStagePullbackComparison l Ω f B L _).hom ≫
            (r D l hl Ω f L).map b ≫ (commonStagePullbackComparison l Ω f B' L _).inv)
      apply (mapHEq (tOmega D l hl Ω Y)
        (congrArg₂ Prod.mk (rOmega_obj D l hl Ω f A) (rOmega_obj D l hl Ω f B))
        (congrArg₂ Prod.mk (rOmega_obj D l hl Ω f A') (rOmega_obj D l hl Ω f B')) hp).trans
      apply ht.trans
      apply heq_of_eq
      change ofHom (target D l hl Ω f A B) (target D l hl Ω f A' B') L h h' _ = _
      apply congrArg (ofHom (target D l hl Ω f A B)
        (target D l hl Ω f A' B') L h h')
      exact tensorCoordinate (t D l hl Ω Y L)
        (commonStagePullbackComparison l Ω f A L _)
        (commonStagePullbackComparison l Ω f B L _)
        (commonStagePullbackComparison l Ω f A' L _)
        (commonStagePullbackComparison l Ω f B' L _)
        (commonStageTensorComparison l Ω Y
          (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h)
        (commonStageTensorComparison l Ω Y
          (commonStagePullbackObject l Ω f A') (commonStagePullbackObject l Ω f B') L h')
        ((r D l hl Ω f L).map a) ((r D l hl Ω f L).map b)


set_option allowUnsafeReducibility true in
attribute [local reducible] b theta

/-- The tensor part of common-stage descent, isolated from the unit and path clauses.
Source: def-pur-section-invariant, final invertibility assertion, DAG subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent).
The proof constructs the representative at a compositum and checks enlargement,
representative independence, and naturality using the mixed tensor square and the
scalar tower comparisons. -/
private theorem tensorDescentCore
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of D.k))]
    (mu : ∀ E : Index l Ω,
      t D l hl Ω X E ⋙ r D l hl Ω f E ≅
        (r D l hl Ω f E).prod (r D l hl Ω f E) ⋙ t D l hl Ω Y E)
    (mixedTensor : ∀ (E L : Index l Ω) (h : E ≤ L) (M N : Stage l Ω X E),
      (transition l Ω Y E L h).map ((mu E).hom.app (M, N)) ≫
        (theta D l hl Ω Y E L h).hom.app
          ((r D l hl Ω f E).obj M, (r D l hl Ω f E).obj N) ≫
        (t D l hl Ω Y L).map (Prod.mkHom
          ((b D l hl Ω f E L h).hom.app M) ((b D l hl Ω f E L h).hom.app N)) =
      (b D l hl Ω f E L h).hom.app ((t D l hl Ω X E).obj (M, N)) ≫
        (r D l hl Ω f L).map ((theta D l hl Ω X E L h).hom.app (M, N)) ≫
        (mu L).hom.app ((transition l Ω X E L h).obj M,
          (transition l Ω X E L h).obj N)) :
    ∃ muOmega : tOmega D l hl Ω X ⋙ rOmega D l hl Ω f ≅
        (rOmega D l hl Ω f).prod (rOmega D l hl Ω f) ⋙ tOmega D l hl Ω Y,
      ∀ (A B : Pair l Ω X) (L : Index l Ω)
        (h : (source D l hl Ω f A B).stage ≤ L),
        HEq (muOmega.hom.app (A, B))
          (ofHom (source D l hl Ω f A B) (target D l hl Ω f A B) L h h
            ((sourceComparison D l hl Ω f A B L h).hom ≫
              (mu L).hom.app
                (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                  A.stage B.stage).1.trans h),
                B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                  A.stage B.stage).2.trans h)) ≫
              (targetComparison D l hl Ω f A B L h).inv)) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      let _ := residueUnits D l hl X
      let _ := residueUnits D l hl Y
      let F := tOmega D l hl Ω X ⋙ rOmega D l hl Ω f
      let G := (rOmega D l hl Ω f).prod (rOmega D l hl Ω f) ⋙ tOmega D l hl Ω Y
      let c (A B : Pair l Ω X) (L : Index l Ω)
          (h : (source D l hl Ω f A B).stage ≤ L) :=
        sourceComparison D l hl Ω f A B L h ≪≫
          (mu L).app
            (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
              A.stage B.stage).1.trans h),
             B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
              A.stage B.stage).2.trans h)) ≪≫
          (targetComparison D l hl Ω f A B L h).symm
      let d (A B : Pair l Ω X) :=
        representativeIso (stageSystem l Ω Y) (source D l hl Ω f A B)
          (target D l hl Ω f A B) (source D l hl Ω f A B).stage le_rfl le_rfl
            (c A B (source D l hl Ω f A B).stage le_rfl)
      let e (A B : Pair l Ω X) : F.obj (A, B) ≅ G.obj (A, B) :=
        eqToIso (source_obj D l hl Ω f A B) ≪≫ d A B ≪≫
          (eqToIso (target_obj D l hl Ω f A B)).symm
      have he (A B : Pair l Ω X) (L : Index l Ω)
          (h : (source D l hl Ω f A B).stage ≤ L) :
          HEq (e A B).hom
            (ofHom (source D l hl Ω f A B) (target D l hl Ω f A B) L h h
              (c A B L h).hom) := by
        have hbase : HEq (e A B).hom
            (ofHom (source D l hl Ω f A B) (target D l hl Ω f A B)
              (source D l hl Ω f A B).stage le_rfl le_rfl
              (c A B (source D l hl Ω f A B).stage le_rfl).hom) := by
          exact (isoConjHEq (source_obj D l hl Ω f A B)
            (target_obj D l hl Ω f A B) (d A B)).trans (heq_of_eq
              (representativeIso_hom (stageSystem l Ω Y)
                (source D l hl Ω f A B) (target D l hl Ω f A B)
                (source D l hl Ω f A B).stage le_rfl le_rfl
                (c A B (source D l hl Ω f A B).stage le_rfl)))
        apply hbase.trans
        apply heq_of_eq
        have ht := restrictionTensorRepresentativeTransport l Ω f mu (by
          intro E L h M N
          have hm := mixedTensor E L h M N
          dsimp only [r, t, b, theta] at hm ⊢
          exact hm) A B L h
        dsimp only [c, sourceComparison, targetComparison, r, t, source, target,
          Iso.trans_hom, Iso.symm_hom, Iso.app_hom] at ht ⊢
        exact ht
      let eta : F ≅ G := NatIso.ofComponents (fun P ↦ e P.1 P.2) (by
        intro P Q v
        rcases P with ⟨A, B⟩
        rcases Q with ⟨A', B'⟩
        rcases v with ⟨a, b⟩
        let H := (source D l hl Ω f A B).stage
        let H' := (source D l hl Ω f A' B').stage
        let M := Padic.finiteCoefficientCompositum l Ω H H'
        obtain ⟨L, hML, hA, hA', hB, hB', u, v, ha, hb⟩ :=
          StageSystem.PairCategory.exists_common_stage a b M
        have h : H ≤ L := ((Padic.finiteCoefficientFields_properties l Ω).1 H H').1.trans hML
        have h' : H' ≤ L := ((Padic.finiteCoefficientFields_properties l Ω).1 H H').2.trans hML
        subst a
        subst b
        have hF := source_map D l hl Ω f A B A' B' L h h' u v
        have hG := target_map D l hl Ω f A B A' B' L h h' u v
        have hleft := heq_comp (source_obj D l hl Ω f A B)
          (source_obj D l hl Ω f A' B') (target_obj D l hl Ω f A' B') hF (he A' B' L h')
        have hright := heq_comp (source_obj D l hl Ω f A B)
          (target_obj D l hl Ω f A B) (target_obj D l hl Ω f A' B') (he A B L h) hG
        apply eq_of_heq (hleft.trans ((heq_of_eq ?_).trans hright.symm))
        rw [StageSystem.PairCategory.mkHom_comp_mkHom,
          StageSystem.PairCategory.mkHom_comp_mkHom]
        apply congrArg (ofHom (source D l hl Ω f A B)
          (target D l hl Ω f A' B') L h h')
        exact conjugateNaturality _ _ (mu L) (Prod.mkHom u v)
          (sourceComparison D l hl Ω f A B L h)
          (sourceComparison D l hl Ω f A' B' L h')
          (targetComparison D l hl Ω f A B L h)
          (targetComparison D l hl Ω f A' B' L h'))
      exact ⟨eta, he⟩


set_option linter.defProp false in
/-- The base coefficient field is contained in every finite stage.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def baseInclusion (E : Index l Ω) : Padic.finiteCoefficientBase l Ω ≤ E :=
  @bot_le (IntermediateField (Padic l) Ω) _ _ E.val

/-- The common-stage coefficient unit is represented over the base field.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def unitPair (W : Scheme.{u}) [W.Over (Spec (.of D.k))] : Pair l Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    unit D l hl Ω W (Padic.finiteCoefficientBase l Ω)⟩

/-- The scalar-unit identification for the target unit at any stage.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def unitTargetComparison (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    (unitPair D l hl Ω W).toStage (baseInclusion l Ω E) ≅ unit D l hl Ω W E :=
  (operationStageTransitionIso l Ω W (Padic.finiteCoefficientBase l Ω) E
    (baseInclusion l Ω E)).app _ ≪≫
      upsilon D l hl Ω W (Padic.finiteCoefficientBase l Ω) E (baseInclusion l Ω E)

/-- The literal source pair of the coefficient-unit comparison.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
@[reducible] def unitSource {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  ⟨Padic.finiteCoefficientBase l Ω,
    (r D l hl Ω f (Padic.finiteCoefficientBase l Ω)).obj
      (unit D l hl Ω X (Padic.finiteCoefficientBase l Ω))⟩

/-- The source-unit identification combines restriction and normalized scalar units.
Source: def-pur-section-invariant, common-stage subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent). -/
def unitSourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) :
    (unitSource D l hl Ω f).toStage (baseInclusion l Ω E) ≅
      (r D l hl Ω f E).obj (unit D l hl Ω X E) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  let E₀ := Padic.finiteCoefficientBase l Ω
  let U := unit D l hl Ω X E₀
  let R₀ := r D l hl Ω f E₀
  let R₁ := r D l hl Ω f E
  let x := operationStageTransitionIso l Ω X E₀ E (baseInclusion l Ω E)
  let y := operationStageTransitionIso l Ω Y E₀ E (baseInclusion l Ω E)
  (y.app (R₀.obj U) ≪≫ (b D l hl Ω f E₀ E (baseInclusion l Ω E)).app U ≪≫
    R₁.mapIso (x.app U).symm) ≪≫
    R₁.mapIso (unitTargetComparison D l hl Ω X E)


attribute [local irreducible] unit upsilon baseInclusion
  Padic.finiteCoefficientBase Padic.coefficientExtensionIntegers

set_option allowUnsafeReducibility true in
attribute [local reducible] unitSourceComparison unitTargetComparison
  commonStagePullbackComparison

/-- The coefficient-unit part of common-stage descent, isolated from tensor descent.
Source: def-pur-section-invariant, final invertibility assertion, DAG subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent).
The proof uses the normalized constant coefficient unit, the mixed unit square,
and the scalar-unit tower to show that all finite representatives define one class. -/
private theorem unitDescentCore
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of D.k))]
    (epsilon : ∀ E : Index l Ω,
      (r D l hl Ω f E).obj (unit D l hl Ω X E) ≅ unit D l hl Ω Y E)
    (mixedUnit : ∀ (E L : Index l Ω) (h : E ≤ L),
      (transition l Ω Y E L h).map (epsilon E).hom ≫
        (upsilon D l hl Ω Y E L h).hom =
      (b D l hl Ω f E L h).hom.app (unit D l hl Ω X E) ≫
        (r D l hl Ω f L).map (upsilon D l hl Ω X E L h).hom ≫ (epsilon L).hom) :
    ∃ epsilonOmega :
        (rOmega D l hl Ω f).obj (unitPair D l hl Ω X) ≅ unitPair D l hl Ω Y,
      ∀ E : Index l Ω,
        HEq epsilonOmega.hom
          (ofHom (unitSource D l hl Ω f) (unitPair D l hl Ω Y) E
            (baseInclusion l Ω E) (baseInclusion l Ω E)
            ((unitSourceComparison D l hl Ω f E).hom ≫ (epsilon E).hom ≫
              (unitTargetComparison D l hl Ω Y E).inv)) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      let _ := residueUnits D l hl X
      let _ := residueUnits D l hl Y
      let E₀ := Padic.finiteCoefficientBase l Ω
      let U := unit D l hl Ω X E₀
      let V := unit D l hl Ω Y E₀
      let I := inclusion (l := l) (Ω := Ω) (Y := Y) E₀
      have hobj : (rOmega D l hl Ω f).obj (unitPair D l hl Ω X) =
          unitSource D l hl Ω f := by
        unfold rOmega commonStageDerivedPullback unitSource
        exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _
      let e : (rOmega D l hl Ω f).obj (unitPair D l hl Ω X) ≅
          unitPair D l hl Ω Y :=
        eqToIso hobj ≪≫ I.mapIso (epsilon E₀)
      refine ⟨e, ?_⟩
      intro E
      let h := baseInclusion l Ω E
      have hmix := mixedUnit E₀ E h
      have hcoord :
          (unitSourceComparison D l hl Ω f E).hom ≫ (epsilon E).hom ≫
            (unitTargetComparison D l hl Ω Y E).inv =
          ((stageSystem l Ω Y).T h).map (epsilon E₀).hom := by
        exact unitCoordinate (r D l hl Ω f E₀) (r D l hl Ω f E)
          (transition l Ω X E₀ E h) (transition l Ω Y E₀ E h)
          ((stageSystem l Ω X).T h) ((stageSystem l Ω Y).T h)
          (operationStageTransitionIso l Ω X E₀ E h)
          (operationStageTransitionIso l Ω Y E₀ E h)
          (b D l hl Ω f E₀ E h)
          U V (unit D l hl Ω X E) (unit D l hl Ω Y E) (epsilon E₀) (epsilon E)
          (upsilon D l hl Ω X E₀ E h) (upsilon D l hl Ω Y E₀ E h) hmix
      have he : HEq e.hom (I.map (epsilon E₀).hom) := by
        dsimp only [e, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
        exact eqToHom_comp_heq (I.map (epsilon E₀).hom) hobj
      apply he.trans
      apply heq_of_eq
      rw [StageSystem.ι_map_eq h]
      exact congrArg (ofHom (unitSource D l hl Ω f) (unitPair D l hl Ω Y) E h h)
        hcoord.symm


/-- Compatible natural tensor and unit comparisons descend to the raw pair category.
Source: def-pur-section-invariant, final invertibility assertion, DAG subargument
(blueprint: lem-pur-common-stage-restriction-tensor-descent).

Proof in words, following the eight DAG steps:
1. Use the recorded restriction and tensor functors and scalar comparison towers.
2. At H=EF form c_H=(b_M inverse tensor b_N inverse) mu_H. Its inverse is
   mu_H inverse followed by (b_M tensor b_N); both inverse identities hold at H.
3. Rearrange the mixed tensor square by cancelling b_M tensor b_N.
4. Use the specified scalar associators to identify both endpoints at K above H.
   Restriction tower compatibility reads b_KE y = r_K(x) b_KH S(b_HE).
5. Tensor-comparison naturality, the rearranged square and this tower identity
   give q S(c_H)=c_K p. A further compositum compares incomparable fields and
   proves equality of classes and their inverses.
6. Represent arbitrary input arrows at one field L. Their images are conjugated
   by b, and naturality of mu_L gives the tensor square there. Restoring endpoint
   comparisons restores exactly the theta conjugations in the actual arrow action.
7. The mixed unit square gives the identical transport calculation for epsilon;
   normalized scalar-unit identifications identify every unit stage with the base.
8. Every specified finite structural equation involves finitely many arrows.
   Extend them to one field, use steps 5--7, and cancel intermediate endpoint
   isomorphisms. Inclusion is a functor, so it preserves that equation, identities
   and composition. No idempotent completion or full faithfulness is used. -/
theorem descent
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of D.k))]
    (mu : ∀ E : Index l Ω,
      t D l hl Ω X E ⋙ r D l hl Ω f E ≅
        (r D l hl Ω f E).prod (r D l hl Ω f E) ⋙ t D l hl Ω Y E)
    (epsilon : ∀ E : Index l Ω,
      (r D l hl Ω f E).obj (unit D l hl Ω X E) ≅ unit D l hl Ω Y E)
    (mixedTensor : ∀ (E L : Index l Ω) (h : E ≤ L) (M N : Stage l Ω X E),
      (transition l Ω Y E L h).map ((mu E).hom.app (M, N)) ≫
        (theta D l hl Ω Y E L h).hom.app
          ((r D l hl Ω f E).obj M, (r D l hl Ω f E).obj N) ≫
        (t D l hl Ω Y L).map (Prod.mkHom
          ((b D l hl Ω f E L h).hom.app M) ((b D l hl Ω f E L h).hom.app N)) =
      (b D l hl Ω f E L h).hom.app ((t D l hl Ω X E).obj (M, N)) ≫
        (r D l hl Ω f L).map ((theta D l hl Ω X E L h).hom.app (M, N)) ≫
        (mu L).hom.app ((transition l Ω X E L h).obj M,
          (transition l Ω X E L h).obj N))
    (mixedUnit : ∀ (E L : Index l Ω) (h : E ≤ L),
      (transition l Ω Y E L h).map (epsilon E).hom ≫
        (upsilon D l hl Ω Y E L h).hom =
      (b D l hl Ω f E L h).hom.app (unit D l hl Ω X E) ≫
        (r D l hl Ω f L).map (upsilon D l hl Ω X E L h).hom ≫ (epsilon L).hom) :
    ∃ muOmega : tOmega D l hl Ω X ⋙ rOmega D l hl Ω f ≅
        (rOmega D l hl Ω f).prod (rOmega D l hl Ω f) ⋙ tOmega D l hl Ω Y,
      (∀ (A B : Pair l Ω X) (L : Index l Ω)
        (h : (source D l hl Ω f A B).stage ≤ L),
        HEq (muOmega.hom.app (A, B))
          (ofHom (source D l hl Ω f A B) (target D l hl Ω f A B) L h h
            ((sourceComparison D l hl Ω f A B L h).hom ≫
              (mu L).hom.app
                (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                  A.stage B.stage).1.trans h),
                B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                  A.stage B.stage).2.trans h)) ≫
              (targetComparison D l hl Ω f A B L h).inv))) ∧
      (∃ epsilonOmega :
        (rOmega D l hl Ω f).obj (unitPair D l hl Ω X) ≅ unitPair D l hl Ω Y,
        ∀ E : Index l Ω,
          HEq epsilonOmega.hom
            (ofHom (unitSource D l hl Ω f) (unitPair D l hl Ω Y) E
              (baseInclusion l Ω E) (baseInclusion l Ω E)
              ((unitSourceComparison D l hl Ω f E).hom ≫ (epsilon E).hom ≫
                (unitTargetComparison D l hl Ω Y E).inv))) ∧
      (∀ (E : Index l Ω) (M N : Stage l Ω Y E) (p q : Quiver.Path M N),
        composePath p = composePath q →
          composePath ((inclusion (l := l) (Ω := Ω) (Y := Y) E).toPrefunctor.mapPath p) =
            composePath ((inclusion (l := l) (Ω := Ω) (Y := Y) E).toPrefunctor.mapPath q)) := by
  obtain ⟨muOmega, hmu⟩ := tensorDescentCore D l hl Ω f mu mixedTensor
  obtain ⟨epsilonOmega, hepsilon⟩ := unitDescentCore D l hl Ω f epsilon mixedUnit
  refine ⟨muOmega, hmu, ⟨epsilonOmega, hepsilon⟩, ?_⟩
  intro E M N p q hpq
  let F := inclusion (l := l) (Ω := Ω) (Y := Y) E
  have hmap : ∀ {M N : Stage l Ω Y E} (p : Quiver.Path M N),
      composePath (F.toPrefunctor.mapPath p) = F.map (composePath p) := by
    intro M N p
    induction p with
    | nil => exact (F.map_id _).symm
    | cons p e ih =>
        change composePath (F.toPrefunctor.mapPath p) ≫ F.map e =
          F.map (composePath p ≫ e)
        rw [ih, F.map_comp]
        rfl
  rw [hmap p, hmap q, hpq]


end WeilConjectures.CommonStageRestrictionTensor
