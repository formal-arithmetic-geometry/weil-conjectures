/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q98, T9
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility

/-! # Simultaneous common-stage Hom lifting

Source: main-20261015, def-pur-section-invariant, final invertibility assertion,
finite-clopen coefficient transport, original steps 8--9 and 11; the agent subargument
specified in the DAG (blueprint: lem-pur-common-stage-finite-hom-lifting).

The restriction maps below only expose the existing canonical pullback on its literal
pair objects. Scalar transport and all coefficient categories are the recorded ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u w
open CategoryTheory AlgebraicGeometry
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient)
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] WeilConjectures.commonStagePullbackComparison
  WeilConjectures.rationalDerivedPullback

attribute [local implicit_reducible] catToReflQuiver Stage stageCategory StageHom
  WeilConjectures.commonStagePullbackObject

namespace WeilConjectures.CommonStageFiniteHomLifting

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (P : PurityFiniteSetting.{u})

/-- The source-implied residue-field inverse, obtained by mapping the existing stalk
inverse. Source: purity conventions, ell distinct from p
(blueprint: lem-pur-common-stage-finite-hom-lifting). -/
@[instance_reducible]
def residueInvertible (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    Invertible (P.coefficients.l : Y.left.residueField y) :=
  letI := (P.coefficientPrime_isUnit_stalk Y.left Y.hom y).invertible
  (Invertible.map (IsLocalRing.residue (Y.left.presheaf.stalk y))
    (P.coefficients.l : Y.left.presheaf.stalk y)).copy _ (map_natCast _ _).symm

attribute [instance] residueInvertible

/-- Canonical restriction of a Hom class, identifying the functor's objects with its
specified literal pairs. Source: common-stage pullback formula
(blueprint: lem-pur-common-stage-finite-hom-lifting). -/
def restrictionHom {X Y : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (A B : Pair P.coefficients.l P.coefficients.Qbar X.left) (a : A ⟶ B) :
    commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left A ⟶
      commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left B :=
  eqToHom ((commonStageDerivedPullback_existsUnique
      P.coefficients.l P.coefficients.Qbar j.left).exists.choose_spec.1 A).symm ≫
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left).map a ≫
    eqToHom ((commonStageDerivedPullback_existsUnique
      P.coefficients.l P.coefficients.Qbar j.left).exists.choose_spec.1 B)

/-- The prescribed conjugated representative, with the existing normalized rational
pullback/scalar comparisons. Source: common-stage pullback formula
(blueprint: lem-pur-common-stage-finite-hom-lifting). -/
def stageRestriction {X Y : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (A B : Pair P.coefficients.l P.coefficients.Qbar X.left) (L : Common A B)
    (a : StageHom A B L) :
    StageHom (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left A)
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left B)
      ⟨L.val, L.property⟩ :=
  (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar j.left
      A L.val L.property.1).hom ≫
    (rationalDerivedPullback P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L.val) j.left).map a ≫
    (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar j.left
      B L.val L.property.2).inv

private theorem restrictionHom_ofHom
    {X Y : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (A B : Pair P.coefficients.l P.coefficients.Qbar X.left) (L : Common A B)
    (a : StageHom A B L) :
    restrictionHom P j A B (ofHom A B L.val L.property.1 L.property.2 a) =
      ofHom (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left B)
        L.val L.property.1 L.property.2 (stageRestriction P j A B L a) := by
  dsimp only [restrictionHom]
  symm
  exact (CategoryTheory.conj_eqToHom_iff_heq _ _
    ((commonStageDerivedPullback_existsUnique
      P.coefficients.l P.coefficients.Qbar j.left).exists.choose_spec.1 A).symm
    ((commonStageDerivedPullback_existsUnique
      P.coefficients.l P.coefficients.Qbar j.left).exists.choose_spec.1 B).symm).mpr
    ((commonStageDerivedPullback_existsUnique
      P.coefficients.l P.coefficients.Qbar j.left).exists.choose_spec.2
        A B L.val L.property.1 L.property.2 a).symm

private theorem stageRestriction_transport
    {X Y : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (A B : Pair P.coefficients.l P.coefficients.Qbar X.left)
    (L N : Common A B) (h : L ≤ N) (a : StageHom A B L) :
    stageRestriction P j A B N (transport A B L N h a) =
      transport (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar j.left B)
        ⟨L.val, L.property⟩ ⟨N.val, N.property⟩ h
        (stageRestriction P j A B L a) := by
  obtain ⟨⟨Φ, β, coh⟩, hΦ, hβ, _⟩ :=
    (sfRationalDirectImageCoefficientCompatibility
      P.coefficients.l P.coefficients.Qbar j.left).exists
  dsimp only at hΦ
  subst Φ
  let F : (stageSystem P.coefficients.l P.coefficients.Qbar X.left).Morphism
      (stageSystem P.coefficients.l P.coefficients.Qbar Y.left) :=
    ⟨_, β, coh⟩
  have haL := congrArg Iso.hom (eq_of_heq
    (hβ A.stage L.val L.property.1 A.obj))
  have hbL := congrArg Iso.inv (eq_of_heq
    (hβ B.stage L.val L.property.2 B.obj))
  have haN := congrArg Iso.hom (eq_of_heq
    (hβ A.stage N.val N.property.1 A.obj))
  have hbN := congrArg Iso.inv (eq_of_heq
    (hβ B.stage N.val N.property.2 B.obj))
  dsimp only [Iso.app_hom, Iso.app_inv] at haL hbL haN hbN
  have ht := F.tr_mapAt (hi := L.property.1) (hj := L.property.2)
    (x := A.obj) (y := B.obj) h a
  dsimp only [StageSystem.Morphism.mapAt, F] at ht
  rw [haL, hbL, haN, hbN] at ht
  exact ht.symm

private theorem finiteUpper
    {Y : Scheme.{u}} (A B : Pair P.coefficients.l P.coefficients.Qbar Y)
    (S : Finset (Index P.coefficients.l P.coefficients.Qbar)) :
    ∃ L : Common A B, ∀ E ∈ S, E ≤ L.val := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨Classical.choice inferInstance, by simp⟩
  | @insert E S _ ih =>
    obtain ⟨L, hL⟩ := ih
    let N := Padic.finiteCoefficientCompositum P.coefficients.l P.coefficients.Qbar L.val E
    have h := (Padic.finiteCoefficientFields_properties
      P.coefficients.l P.coefficients.Qbar).1 L.val E
    refine ⟨⟨N, L.property.1.trans h.1, L.property.2.trans h.1⟩, ?_⟩
    intro F hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact h.2
    · exact (hL F hF).trans h.1

private theorem ofHom_transport
    {Y : Scheme.{u}} (A B : Pair P.coefficients.l P.coefficients.Qbar Y)
    (L N : Common A B) (h : L ≤ N) (a : StageHom A B L) :
    ofHom A B N.val N.property.1 N.property.2 (transport A B L N h a) =
      ofHom A B L.val L.property.1 L.property.2 a := by
  exact StageSystem.PairCategory.mkHom_tr (X := A) (Y := B) h a

private theorem transport_trans
    {Y : Scheme.{u}} (A B : Pair P.coefficients.l P.coefficients.Qbar Y)
    (L M N : Common A B) (h : L ≤ M) (k : M ≤ N) (a : StageHom A B L) :
    transport A B M N k (transport A B L M h a) = transport A B L N (h.trans k) a := by
  exact StageSystem.tr_tr (S := stageSystem P.coefficients.l P.coefficients.Qbar Y)
    (hi := L.property.1) (hj := L.property.2) (x := A.obj) (y := B.obj) h k a


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


variable {I : Type w} [Finite I]
  (X : Over (Spec (CommRingCat.of P.field.k)))
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)

/-- Simultaneous lifting, bijectivity and eventual equality, including the empty family.
Source: main-20261015, def-pur-section-invariant, finite-clopen transport, original
steps 8--9 and 11 (blueprint: lem-pur-common-stage-finite-hom-lifting).

Proof: the unique coherent pullback family in
sfRationalDirectImageCoefficientCompatibility has exactly the rational pullback
functors and the prescribed comparison components. Its tr_mapAt law gives
stageRestriction_transport. The representative formula for the chosen common-stage
pullback gives restrictionHom_ofHom.

Represent the finitely many local arrows and take a finite compositum of their
fields, the endpoints, and the prescribed extra fields. Conjugate the transported
arrows by the inverse source and target comparisons. Stagewise fullness lifts this
tuple; cancelling the comparisons proves simultaneous lifting and surjectivity.
This also works at any specified common upper field.

For component equalities, take their actual eventual-equality witnesses. Transport
each equality to any common upper field. Transport composition and compatibility
with restriction identify these equalities with restrictions of global transports.
Cancelling comparisons and using stagewise faithfulness equates the global
transports. The representative equality criterion gives injectivity and the stated
eventual-equality equivalence. No injectivity of Hom transition maps is used.

For an empty family, surjectivity lifts the empty tuple and injectivity equates any
two arrows. Finite-compositum induction starts with a common endpoint field even
when the list of extra fields is empty. -/
theorem finiteHomLifting
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [∀ i, LocallyOfFiniteType (Xi i).hom] [∀ i, QuasiCompact (Xi i).hom]
    (hfully : ∀ (E : Index P.coefficients.l P.coefficients.Qbar)
      (K M : Stage P.coefficients.l P.coefficients.Qbar X.left E),
      Function.Bijective (fun a : K ⟶ M ↦ fun i : I ↦
        (rationalDerivedPullback P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (j i).left).map a))
    (A B : Pair P.coefficients.l P.coefficients.Qbar X.left) :
    Function.Bijective (fun a : A ⟶ B ↦ fun i : I ↦ restrictionHom P (j i) A B a) ∧
    (∀ (L : Common A B) (a : StageHom A B L) (i : I),
      restrictionHom P (j i) A B (ofHom A B L.val L.property.1 L.property.2 a) =
        ofHom
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
          L.val L.property.1 L.property.2 (stageRestriction P (j i) A B L a)) ∧
    (∀ (v : ∀ i : I,
        commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A ⟶
          commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
      (S : Finset (Index P.coefficients.l P.coefficients.Qbar)),
      ∃ (L : Common A B), (∀ E ∈ S, E ≤ L.val) ∧
        ∃ a : StageHom A B L, ∀ i : I,
          restrictionHom P (j i) A B (ofHom A B L.val L.property.1 L.property.2 a) = v i) ∧
    (∀ (Li : ∀ i : I,
        Common (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B))
      (v : ∀ i : I, StageHom _ _ (Li i))
      (L : Common A B) (hL : ∀ i : I, (Li i).val ≤ L.val),
      ∃ a : StageHom A B L, ∀ i : I,
        (rationalDerivedPullback P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L.val) (j i).left).map a =
        (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left
            A L.val L.property.1).inv ≫
          transport _ _ (Li i) ⟨L.val, L.property⟩ (hL i) (v i) ≫
          (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left
            B L.val L.property.2).hom) ∧
    (∀ (L₀ L₁ : Common A B) (a₀ : StageHom A B L₀) (a₁ : StageHom A B L₁),
      (∀ i : I,
        restrictionHom P (j i) A B (ofHom A B L₀.val L₀.property.1 L₀.property.2 a₀) =
          restrictionHom P (j i) A B (ofHom A B L₁.val L₁.property.1 L₁.property.2 a₁)) ↔
      ∃ (N : Common A B) (h₀ : L₀ ≤ N) (h₁ : L₁ ≤ N),
        transport A B L₀ N h₀ a₀ = transport A B L₁ N h₁ a₁) ∧
    (∀ (L₀ L₁ : Common A B) (a₀ : StageHom A B L₀) (a₁ : StageHom A B L₁)
      (Ni : I → Common A B) (h₀ : ∀ i : I, L₀ ≤ Ni i) (h₁ : ∀ i : I, L₁ ≤ Ni i),
      (∀ i : I,
        transport
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
          ⟨L₀.val, L₀.property⟩ ⟨(Ni i).val, (Ni i).property⟩ (h₀ i)
            (stageRestriction P (j i) A B L₀ a₀) =
          transport
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
            ⟨L₁.val, L₁.property⟩ ⟨(Ni i).val, (Ni i).property⟩ (h₁ i)
            (stageRestriction P (j i) A B L₁ a₁)) →
      ∀ (N : Common A B) (k₀ : L₀ ≤ N) (k₁ : L₁ ≤ N),
        (∀ i : I, Ni i ≤ N) →
        transport A B L₀ N k₀ a₀ = transport A B L₁ N k₁ a₁) ∧
    (IsEmpty I → Nonempty (A ⟶ B) ∧ Subsingleton (A ⟶ B)) := by
  classical
  let := Fintype.ofFinite I
  have liftAt (Li : ∀ i : I,
      Common (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B))
      (v : ∀ i : I, StageHom _ _ (Li i))
      (L : Common A B) (hL : ∀ i : I, (Li i).val ≤ L.val) :=
    (hfully L.val (A.toStage L.property.1) (B.toStage L.property.2)).2
      (fun i ↦
        (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left
            A L.val L.property.1).inv ≫
          transport _ _ (Li i) ⟨L.val, L.property⟩ (hL i) (v i) ≫
          (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left
            B L.val L.property.2).hom)
  have faithAt (L : Common A B) (a b : StageHom A B L)
      (h : ∀ i, stageRestriction P (j i) A B L a =
        stageRestriction P (j i) A B L b) : a = b := by
    apply (hfully L.val (A.toStage L.property.1) (B.toStage L.property.2)).1
    funext i
    let s := commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
      (j i).left A L.val L.property.1
    let t := commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
      (j i).left B L.val L.property.2
    have hi : s.hom ≫
        (rationalDerivedPullback P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L.val) (j i).left).map a ≫
          t.inv = s.hom ≫
        (rationalDerivedPullback P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L.val) (j i).left).map b ≫
          t.inv := h i
    apply (cancel_epi s.hom).mp
    apply (cancel_mono t.inv).mp
    exact (Category.assoc _ _ _).trans hi |>.trans (Category.assoc _ _ _).symm
  have witnesses (L₀ L₁ : Common A B) (a₀ : StageHom A B L₀) (a₁ : StageHom A B L₁)
      (Ni : I → Common A B) (h₀ : ∀ i, L₀ ≤ Ni i) (h₁ : ∀ i, L₁ ≤ Ni i)
      (he : ∀ i,
        transport
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
          ⟨L₀.val, L₀.property⟩ ⟨(Ni i).val, (Ni i).property⟩ (h₀ i)
          (stageRestriction P (j i) A B L₀ a₀) =
        transport
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
          ⟨L₁.val, L₁.property⟩ ⟨(Ni i).val, (Ni i).property⟩ (h₁ i)
          (stageRestriction P (j i) A B L₁ a₁))
      (N : Common A B) (k₀ : L₀ ≤ N) (k₁ : L₁ ≤ N) (k : ∀ i, Ni i ≤ N) :
      transport A B L₀ N k₀ a₀ = transport A B L₁ N k₁ a₁ := by
    apply faithAt N
    intro i
    rw [stageRestriction_transport, stageRestriction_transport]
    have ht := congrArg (transport
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
      ⟨(Ni i).val, (Ni i).property⟩ ⟨N.val, N.property⟩ (k i)) (he i)
    simpa only [transport_trans] using ht
  have injective : Function.Injective
      (fun a : A ⟶ B ↦ fun i : I ↦ restrictionHom P (j i) A B a) := by
    intro a b hab
    obtain ⟨L₀, hA₀, hB₀, a₀, rfl⟩ := (representatives A B).1 a
    obtain ⟨L₁, hA₁, hB₁, a₁, rfl⟩ := (representatives A B).1 b
    let L₀' : Common A B := ⟨L₀, hA₀, hB₀⟩
    let L₁' : Common A B := ⟨L₁, hA₁, hB₁⟩
    have hi (i : I) := (restrictionHom_ofHom P (j i) A B L₀' a₀).symm.trans
      ((congrFun hab i).trans (restrictionHom_ofHom P (j i) A B L₁' a₁))
    have hw (i : I) := (representatives
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)).2
        ⟨L₀, hA₀, hB₀⟩ ⟨L₁, hA₁, hB₁⟩ _ _ |>.mp (hi i)
    choose Ni h₀ h₁ he using hw
    let S := Finset.univ.image (fun i ↦ (Ni i).val) ∪ {L₀, L₁}
    obtain ⟨N, hN⟩ := finiteUpper P A B S
    have k₀ : L₀' ≤ N := hN L₀
      (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
    have k₁ : L₁' ≤ N := hN L₁
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    have k (i : I) : (Ni i).val ≤ N.val := hN _
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    apply (representatives A B).2 L₀' L₁' a₀ a₁ |>.mpr
    exact ⟨N, k₀, k₁, witnesses L₀' L₁' a₀ a₁
      (fun i ↦ ⟨(Ni i).val, (Ni i).property⟩) h₀ h₁ he N k₀ k₁ k⟩
  have simultaneous (v : ∀ i : I,
      commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A ⟶
        commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
      (S : Finset (Index P.coefficients.l P.coefficients.Qbar)) :
      ∃ (L : Common A B), (∀ E ∈ S, E ≤ L.val) ∧
        ∃ a : StageHom A B L, ∀ i,
          restrictionHom P (j i) A B (ofHom A B L.val L.property.1 L.property.2 a) = v i := by
    have hv (i : I) := (representatives
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)).1 (v i)
    choose Li hAi hBi vi hvi using hv
    obtain ⟨L, hL⟩ := finiteUpper P A B (S ∪ Finset.univ.image Li)
    have hLi (i : I) : Li i ≤ L.val := hL _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    obtain ⟨a, ha⟩ := liftAt (fun i ↦ ⟨Li i, hAi i, hBi i⟩) vi L hLi
    refine ⟨L, fun E hE ↦ hL E (Finset.mem_union_left _ hE), a, ?_⟩
    intro i
    apply (restrictionHom_ofHom P (j i) A B L a).trans
    have hai := congrFun ha i
    dsimp only at hai
    have hs : stageRestriction P (j i) A B L a =
        transport
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
          ⟨Li i, hAi i, hBi i⟩ ⟨L.val, L.property⟩ (hLi i) (vi i) := by
      let s := commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
        (j i).left A L.val L.property.1
      let t := commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
        (j i).left B L.val L.property.2
      let vL := transport
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
        ⟨Li i, hAi i, hBi i⟩ ⟨L.val, L.property⟩ (hLi i) (vi i)
      have hc := congrArg (fun f ↦ s.hom ≫ f ≫ t.inv) hai
      apply hc.trans
      calc
        s.hom ≫ (s.inv ≫ vL ≫ t.hom) ≫ t.inv =
            (s.hom ≫ s.inv ≫ vL ≫ t.hom) ≫ t.inv :=
          (Category.assoc _ _ _).symm
        _ = (vL ≫ t.hom) ≫ t.inv :=
          congrArg (fun f ↦ f ≫ t.inv) (s.hom_inv_id_assoc (vL ≫ t.hom))
        _ = vL ≫ (t.hom ≫ t.inv) := Category.assoc _ _ _
        _ = vL := (congrArg (fun f ↦ vL ≫ f) t.hom_inv_id).trans (Category.comp_id vL)
    exact (congrArg
      (ofHom (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
        L.val L.property.1 L.property.2) hs).trans
      ((ofHom_transport P
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B)
        ⟨Li i, hAi i, hBi i⟩ ⟨L.val, L.property⟩ (hLi i) (vi i)).trans (hvi i).symm)
  have surjective : Function.Surjective
      (fun a : A ⟶ B ↦ fun i : I ↦ restrictionHom P (j i) A B a) := by
    intro v
    obtain ⟨L, _, a, ha⟩ := simultaneous v ∅
    exact ⟨ofHom A B L.val L.property.1 L.property.2 a, funext ha⟩
  refine And.intro ⟨injective, surjective⟩ (And.intro ?_
    (And.intro simultaneous (And.intro ?_ (And.intro ?_ (And.intro witnesses ?_)))))
  · intro L a i
    exact restrictionHom_ofHom P (j i) A B L a
  · intro Li v L hL
    exact (liftAt Li v L hL).imp (fun a ha i ↦ congrFun ha i)
  · intro L₀ L₁ a₀ a₁
    rw [← (representatives A B).2 L₀ L₁ a₀ a₁]
    constructor
    · intro h
      exact injective (funext h)
    · intro h i
      exact congrArg (restrictionHom P (j i) A B) h
  · intro hI
    let := hI
    have v : ∀ i : I,
        commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left A ⟶
          commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left B :=
      fun i ↦ isEmptyElim i
    obtain ⟨a, _⟩ := surjective v
    exact ⟨⟨a⟩, ⟨fun b c ↦ @injective b c (funext fun i ↦ isEmptyElim i)⟩⟩

end WeilConjectures.CommonStageFiniteHomLifting
