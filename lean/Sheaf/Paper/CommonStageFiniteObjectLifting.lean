/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.EssentialImage

/-! # Simultaneous finite-field lifting in the raw common-stage categories

Source: main-20261015, sec-six-functors-basics/sk-def-purity-conv,
def-pur-section-invariant, final invertibility assertion, finite-clopen transport
steps 5--7 and empty-family field choice in step 11; the DAG's agent subargument
(blueprint: lem-pur-common-stage-finite-object-lifting).

The component functors and comparisons are the published derived pullbacks and
normalized scalar comparisons. The product is the ordinary Pi-category, including
its empty product. The coefficient closure and finite family have independent sizes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u v w
open CategoryTheory AlgebraicGeometry
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient)
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures.PurityCommonStageLifting

variable (P : PurityFiniteSetting.{u})
  (Ω : Type v) [Field Ω] [Algebra (Padic P.coefficients.l) Ω]
  [IsAlgClosure (Padic P.coefficients.l) Ω]

/-- The coefficient prime is invertible in every residue field occurring over the fixed base.
Source: purity conventions (blueprint: lem-pur-common-stage-finite-object-lifting). -/
@[instance_reducible] def residueInvertible (T : AlgebraicGeometry.Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of P.field.k)) (x : T) :
    Invertible (P.coefficients.l : T.residueField x) := by
  exact (Eq.mp (congrArg IsUnit (map_natCast
    (IsLocalRing.residue (T.presheaf.stalk x)) P.coefficients.l))
    ((P.coefficientPrime_isUnit_stalk T a x).map
      (IsLocalRing.residue (T.presheaf.stalk x)))).invertible

/-- Specialize the existing rational pullback to a morphism over k. The internal
invertibility instances are obtained from the source-implied stalk units, so no
extra geometric hypothesis is imposed. Source: purity conventions and the rational
pullback clause (blueprint: lem-pur-common-stage-finite-object-lifting). -/
def rationalComponent (E : Index P.coefficients.l Ω)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y.left ⟶ X.left) :
    Stage P.coefficients.l Ω X.left E ⥤ Stage P.coefficients.l Ω Y.left E :=
  letI : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    residueInvertible P X.left X.hom
  letI : ∀ y : Y.left, Invertible (P.coefficients.l : Y.left.residueField y) :=
    residueInvertible P Y.left Y.hom
  rationalDerivedPullback P.coefficients.l (Coefficient.{u} P.coefficients.l Ω E) j

/-- Specialize the existing common-stage pullback, retaining the normalized comparison
and the raw pair category. Source: finite-clopen transport steps 5--7
(blueprint: lem-pur-common-stage-finite-object-lifting). -/
def commonComponent
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y.left ⟶ X.left) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left ⥤
      generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω Y.left :=
  letI : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    residueInvertible P X.left X.hom
  letI : ∀ y : Y.left, Invertible (P.coefficients.l : Y.left.residueField y) :=
    residueInvertible P Y.left Y.hom
  commonStageDerivedPullback P.coefficients.l Ω j

/-- The published representative comparison, including its canonical identification
of the stage-system transition with rational scalar extension. Source: finite-clopen
transport step 5 (blueprint: lem-pur-common-stage-finite-object-lifting). -/
def componentComparison
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y.left ⟶ X.left)
    (A : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left)
    (L : Index P.coefficients.l Ω) (h : A.stage ≤ L) :=
  letI : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    residueInvertible P X.left X.hom
  letI : ∀ y : Y.left, Invertible (P.coefficients.l : Y.left.residueField y) :=
    residueInvertible P Y.left Y.hom
  commonStagePullbackComparison P.coefficients.l Ω j A L h

variable {I : Type w}
  (X : Over (Spec (CommRingCat.of P.field.k)))
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, (Xi i).left ⟶ X.left)

/-- The stagewise restriction is the product of the actual rational pullbacks.
Source: finite-clopen transport, essential-surjectivity hypothesis
(blueprint: lem-pur-common-stage-finite-object-lifting). -/
def rationalRestriction (E : Index P.coefficients.l Ω) :=
  Functor.pi' (fun i : I ↦ rationalComponent P Ω E (Y := Xi i) (X := X) (j i))

/-- The requested restriction functor is exactly the product of the published
common-stage pullbacks. Its functor laws include the empty family.
Source: finite-clopen transport steps 5--7
(blueprint: lem-pur-common-stage-finite-object-lifting). -/
def commonRestriction :=
  Functor.pi' (fun i : I ↦ commonComponent P Ω (Y := Xi i) (X := X) (j i))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] operationStageTransitionIso
  ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.unitor commonStagePullbackComparison
  rationalDerivedPullback commonStageDerivedPullback
  GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.transition
  rationalRestriction commonRestriction

attribute [local irreducible] sfIntegralConstructible ScalarLocalization.category
  ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

private def isoOfStageIso {J : Type*} [Preorder J] [IsDirectedOrder J]
    {C : J → Type*} [∀ q, Category (C q)] (S : StageSystem C)
    (A B : S.PairCategory) (L : J) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (t : A.toStage hA ≅ B.toStage hB) : A ≅ B where
  hom := StageSystem.PairCategory.mkHom L hA hB t.hom
  inv := StageSystem.PairCategory.mkHom L hB hA t.inv
  hom_inv_id := by
    rw [StageSystem.PairCategory.mkHom_comp_mkHom, t.hom_inv_id]
    exact (StageSystem.PairCategory.id_eq_mkHom A hA).symm
  inv_hom_id := by
    rw [StageSystem.PairCategory.mkHom_comp_mkHom, t.inv_hom_id]
    exact (StageSystem.PairCategory.id_eq_mkHom B hB).symm

private theorem existsIsoOfThree {J : Type*} [Preorder J] [IsDirectedOrder J]
    {C : J → Type*} [∀ q, Category (C q)] (S : StageSystem C)
    (A B : S.PairCategory) (L : J) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (V W : C L) (a : A.toStage hA ≅ V) (b : W ≅ V) (c : B.toStage hB ≅ W) :
    ∃ e : A ≅ B,
      e.hom = StageSystem.PairCategory.mkHom L hA hB (a.hom ≫ b.inv ≫ c.inv) ∧
      e.inv = StageSystem.PairCategory.mkHom L hB hA (c.hom ≫ b.hom ≫ a.inv) := by
  let t := a ≪≫ b.symm ≪≫ c.symm
  refine ⟨isoOfStageIso S A B L hA hB t, rfl, ?_⟩
  change StageSystem.PairCategory.mkHom L hB hA ((c.hom ≫ b.hom) ≫ a.inv) = _
  rw [Category.assoc]

-- Use the published object formula with the literal stage object visible.
private theorem componentObject_spec
    (A : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left)
    (i : I) :
    (commonRestriction P Ω X Xi j).obj A i =
      ⟨A.stage, (rationalComponent P Ω A.stage (Y := Xi i) (X := X) (j i)).obj A.obj⟩ := by
  let : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    residueInvertible P X.left X.hom
  let : ∀ y : (Xi i).left, Invertible (P.coefficients.l : (Xi i).left.residueField y) :=
    residueInvertible P (Xi i).left (Xi i).hom
  delta commonRestriction
  dsimp only [commonRestriction, Functor.pi', commonComponent, rationalComponent]
  unfold commonStageDerivedPullback
  simpa only [commonStagePullbackObject] using
    (commonStageDerivedPullback_existsUnique.{u, v}
      P.coefficients.l Ω (j i)).exists.choose_spec.1 A

attribute [local implicit_reducible] catToReflQuiver

-- Reduce only the product and pullback wrappers; retain the normalized comparison.
private theorem componentMap_spec :
    ∀ (A B : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left)
      (L : Index P.coefficients.l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (a : A.toStage hA ⟶ B.toStage hB) (i : I),
      HEq ((commonRestriction P Ω X Xi j).map (ofHom A B L hA hB a) i)
        (ofHom
          (⟨A.stage, (rationalComponent P Ω A.stage (Y := Xi i) (X := X) (j i)).obj A.obj⟩ :
            generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω (Xi i).left)
          ⟨B.stage, (rationalComponent P Ω B.stage (Y := Xi i) (X := X) (j i)).obj B.obj⟩ L hA hB
          ((componentComparison P Ω (Y := Xi i) (X := X) (j i) A L hA).hom ≫
            (rationalComponent P Ω L (Y := Xi i) (X := X) (j i)).map a ≫
            (componentComparison P Ω (Y := Xi i) (X := X) (j i) B L hB).inv)) := by
  intro A B L hA hB a i
  let : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    residueInvertible P X.left X.hom
  let : ∀ y : (Xi i).left, Invertible (P.coefficients.l : (Xi i).left.residueField y) :=
    residueInvertible P (Xi i).left (Xi i).hom
  delta commonRestriction
  dsimp only [Functor.pi', commonComponent, rationalComponent]
  unfold commonStageDerivedPullback
  exact (commonStageDerivedPullback_existsUnique.{u, v}
    P.coefficients.l Ω (j i)).exists.choose_spec.2 A B L hA hB a

-- Keep the stage-change calculation outside the large theorem's sealed Stage context.
private theorem stageChange_spec (Y : Scheme.{u})
    (A : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω Y)
    (L : Index P.coefficients.l Ω) (h : A.stage ≤ L) :
    ∃ e : A ≅ (inclusion L).obj
        ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj),
      e.hom = ofHom A ((inclusion L).obj
          ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj)) L h le_rfl
        ((operationStageTransitionIso P.coefficients.l Ω Y A.stage L h).hom.app A.obj ≫
          (unitor P.coefficients.l Ω Y L).inv.app
            ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj) ≫
          (operationStageTransitionIso P.coefficients.l Ω Y L L le_rfl).inv.app
            ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj)) ∧
      e.inv = ofHom ((inclusion L).obj
          ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj)) A L le_rfl h
        ((operationStageTransitionIso P.coefficients.l Ω Y L L le_rfl).hom.app
            ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj) ≫
          (unitor P.coefficients.l Ω Y L).hom.app
            ((transition P.coefficients.l Ω Y A.stage L h).obj A.obj) ≫
          (operationStageTransitionIso P.coefficients.l Ω Y A.stage L h).inv.app A.obj) := by
  let U := (transition P.coefficients.l Ω Y A.stage L h).obj A.obj
  exact existsIsoOfThree (stageSystem P.coefficients.l Ω Y)
    A ((inclusion L).obj U) L h le_rfl U
    ((transition P.coefficients.l Ω Y L L le_rfl).obj U)
    ((operationStageTransitionIso P.coefficients.l Ω Y A.stage L h).app A.obj)
    ((unitor P.coefficients.l Ω Y L).app U)
    ((operationStageTransitionIso P.coefficients.l Ω Y L L le_rfl).app U)

-- The main statement does not need to inspect integral representatives.
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.Stage

/-- Stagewise essential surjectivity gives simultaneous object lifting at the exact
compositum, with the specified representative functor and identity stage changes.
Source: main-20261015 def-pur-section-invariant, final invertibility assertion,
finite-clopen transport steps 5--7 and empty-family field choice in step 11
(blueprint: lem-pur-common-stage-finite-object-lifting).

Proof: (1) For each component conjugate the rational pullback of a representative
by the normalized pullback/scalar comparisons of
lem-pur-integral-operations-scalar-extension. These are rationalized integral maps.
(2) Substitute their tower equation, using the scalar associators of
lem-weil-scalar-extension-composition: extending a conjugated representative equals
conjugating its extension. The eventual-equality characterization in
 def-weil-algebraically-closed-coefficients proves independence of representatives
and common fields. (3) Identity compatibility gives identities. Over one common
field, the middle comparison and its inverse cancel, giving composition. These
componentwise calculations define the Pi functor even for the empty family.
(4) The object and arrow formulas agree with def-weil-derived-pullback-tensor-hom,
so this is exactly its common-stage restriction. (5) Form the finite compositum
of the component stages and the additional list, starting with the base field.
The finite-coefficient-fields definition gives finiteness; the empty collection
gives the base field. Extend each component to this field and apply the assumed
essential surjectivity there, giving K and the component isomorphisms without any
further extension. (6) The stage-change arrows are the identity on the extended
object through the canonical unit identifications. Their composites are identity
classes by scalar identity compatibility. Compose these isomorphisms with those
from step (5) to prove essential surjectivity of the common-stage Pi functor.
Only literal pairs are used; no idempotent completion occurs. -/
theorem finite_object_lifting [Finite I]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [∀ i, LocallyOfFiniteType (Xi i).hom] [∀ i, QuasiCompact (Xi i).hom]
    (hR : ∀ E : Index P.coefficients.l Ω, (rationalRestriction P Ω X Xi j E).EssSurj) :
    (∀ (A : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left)
      (i : I),
      (commonRestriction P Ω X Xi j).obj A i =
        ⟨A.stage, (rationalComponent P Ω A.stage (Y := Xi i) (X := X) (j i)).obj A.obj⟩) ∧
    (∀ (A B : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω X.left)
      (L : Index P.coefficients.l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (a : A.toStage hA ⟶ B.toStage hB) (i : I),
      HEq ((commonRestriction P Ω X Xi j).map (ofHom A B L hA hB a) i)
        (ofHom
          (⟨A.stage, (rationalComponent P Ω A.stage (Y := Xi i) (X := X) (j i)).obj A.obj⟩ :
            generalAlgebraicallyClosedConstructibleCategory P.coefficients.l Ω (Xi i).left)
          ⟨B.stage, (rationalComponent P Ω B.stage (Y := Xi i) (X := X) (j i)).obj B.obj⟩ L hA hB
          ((componentComparison P Ω (Y := Xi i) (X := X) (j i) A L hA).hom ≫
            (rationalComponent P Ω L (Y := Xi i) (X := X) (j i)).map a ≫
            (componentComparison P Ω (Y := Xi i) (X := X) (j i) B L hB).inv))) ∧
    (commonRestriction P Ω X Xi j).EssSurj ∧
    (∀ (A : ∀ i, generalAlgebraicallyClosedConstructibleCategory
          P.coefficients.l Ω (Xi i).left)
      (additional : List (Index P.coefficients.l Ω)),
      ∃ (L : Index P.coefficients.l Ω) (h : ∀ i, (A i).stage ≤ L),
        L.val = (⨆ i, (A i).stage.val) ⊔ (⨆ E ∈ additional, E.val) ∧
        (∀ E ∈ additional, E ≤ L) ∧
        ∃ K : Stage P.coefficients.l Ω X.left L,
          (∀ i, Nonempty ((rationalComponent P Ω L (Y := Xi i) (X := X) (j i)).obj K ≅
            (transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj)) ∧
          (∀ i, ∃ e : A i ≅ (inclusion L).obj
              ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj),
            e.hom = ofHom (A i) ((inclusion L).obj
                ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj))
                L (h i) le_rfl
              ((operationStageTransitionIso P.coefficients.l Ω (Xi i).left
                  (A i).stage L (h i)).hom.app (A i).obj ≫
                (unitor P.coefficients.l Ω (Xi i).left L).inv.app
                  ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj) ≫
                (operationStageTransitionIso P.coefficients.l Ω (Xi i).left
                  L L le_rfl).inv.app
                  ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj)) ∧
            e.inv = ofHom ((inclusion L).obj
                ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj))
                (A i) L le_rfl (h i)
              ((operationStageTransitionIso P.coefficients.l Ω (Xi i).left
                  L L le_rfl).hom.app
                  ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj) ≫
                (unitor P.coefficients.l Ω (Xi i).left L).hom.app
                  ((transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj) ≫
                (operationStageTransitionIso P.coefficients.l Ω (Xi i).left
                  (A i).stage L (h i)).inv.app (A i).obj))) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      have hObj : ∀ (A : generalAlgebraicallyClosedConstructibleCategory
          P.coefficients.l Ω X.left) (i : I),
          (commonRestriction P Ω X Xi j).obj A i =
            ⟨A.stage, (rationalComponent P Ω A.stage (Y := Xi i) (X := X) (j i)).obj A.obj⟩ := by
        exact componentObject_spec P Ω X Xi j
      refine ⟨hObj, ?_, ?_⟩
      · exact componentMap_spec P Ω X Xi j
      · refine (fun hLift ↦ ⟨?_, hLift⟩) ?_
        · intro A additional
          let L : Index P.coefficients.l Ω :=
            ⟨(⨆ i, (A i).stage.val) ⊔ (⨆ E ∈ additional, E.val), by
              have : FiniteDimensional (Padic P.coefficients.l)
                  (⨆ E ∈ additional, E.val : IntermediateField (Padic P.coefficients.l) Ω) := by
                have heq : (⨆ E ∈ additional.toFinset, E.val :
                    IntermediateField (Padic P.coefficients.l) Ω) = (⨆ E ∈ additional, E.val) := by
                  apply iSup_congr
                  intro E
                  exact iSup_congr_Prop List.mem_toFinset (fun _ ↦ rfl)
                rw [← heq]
                infer_instance
              infer_instance⟩
          have h (i : I) : (A i).stage ≤ L :=
            (le_iSup (fun i ↦ (A i).stage.val) i).trans le_sup_left
          refine ⟨L, h, rfl, ?_, ?_⟩
          · intro E hE
            change E.val ≤ (⨆ i, (A i).stage.val) ⊔ (⨆ F ∈ additional, F.val)
            exact (le_iSup_of_le E (le_iSup (fun _ : E ∈ additional ↦ E.val) hE)).trans
              le_sup_right
          · let H (i : I) : Stage P.coefficients.l Ω (Xi i).left L :=
              (transition P.coefficients.l Ω (Xi i).left (A i).stage L (h i)).obj (A i).obj
            have he := (hR L).1 H
            obtain ⟨K, ⟨e⟩⟩ := he
            unfold rationalRestriction at e
            refine ⟨K, fun i ↦ ⟨Pi.isoApp e i⟩, ?_⟩
            intro i
            exact stageChange_spec P Ω ((Xi i).left) (A i) L (h i)
        · refine ⟨?_⟩
          intro A
          obtain ⟨L, h, _, _, K, hK, he⟩ := hLift A []
          refine ⟨(inclusion L).obj K, ⟨Pi.isoMk (fun i ↦ ?_)⟩⟩
          let e₁ : (commonRestriction P Ω X Xi j).obj ((inclusion L).obj K) i ≅
              (inclusion L).obj ((rationalComponent P Ω L (Y := Xi i) (X := X) (j i)).obj K) :=
            eqToIso (hObj ((inclusion L).obj K) i)
          let e₂ := (inclusion L).mapIso (hK i).some
          exact e₁ ≪≫ e₂ ≪≫ (he i).choose.symm

end WeilConjectures.PurityCommonStageLifting
